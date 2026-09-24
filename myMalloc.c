#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>
#include <stdbool.h>

#include "myMalloc.h"

#define MALLOC_COLOR "MALLOC_DEBUG_COLOR"

static bool check_env;
static bool use_color;

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);

// Helper functions for verifying that the data structures are structurally 
// valid
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static void init();

static bool isMallocInitialized;

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}



static inline header * add_to_free_list(header *new) {
  int list_num = (get_size(new) - ALLOC_HEADER_SIZE) / 8 - 1;

  if (list_num >= N_LISTS) {
    list_num = N_LISTS - 1;
  }
  header *freelist = &freelistSentinels[list_num];

  new->next = freelist->next;
  new->prev = freelist;
  freelist->next->prev = new;
  freelist->next = new;
  return new;
}


//taeks in the pointer, needs the size
static inline void remove_from_freelist(header *head, int list_num) {
  head->prev->next = head->next;
  head->next->prev = head->prev;
}

static inline header *coalesse(header *right, header *left) {
  size_t total_size = get_size(right) + get_size(left);
  int list_num = 0;
  int right_state = get_state(right);
  int left_state = get_state(left);
  //remove old list from the free list
  if (right_state == UNALLOCATED) {
    list_num = (get_size(right)  - ALLOC_HEADER_SIZE) / 8 - 1;
    if (list_num >= N_LISTS) {
       list_num = N_LISTS - 1;
    }
    remove_from_freelist(right, list_num);
  }
  if (left_state == UNALLOCATED) {
    list_num = (get_size(left) - ALLOC_HEADER_SIZE) / 8 - 1;
    if (list_num >= N_LISTS) {
      list_num = N_LISTS - 1;
    }
    remove_from_freelist(left, list_num);
  }
  
  set_size_and_state(right, total_size, UNALLOCATED);
  add_to_free_list(right);

  header *next = get_right_header(left);
  next->left_size = get_size(right);
  return right;
}





/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);
  bool lastfence = false;
  if (lastFencePost != NULL) {
    if (get_left_header(mem) == lastFencePost) {
      header *prev = get_left_header(lastFencePost);
      mem = coalesse(lastFencePost, mem);
      mem = coalesse(prev, mem);
      lastfence = true;
    }
  }

  //deleted fencepost from the checker
  /* if ((get_state(right) == UNALLOCATED) &&
    (get_state(left) == UNALLOCATED)) {
    printf("both were unallocated\n");
    header *next_and_free = coalesse(mem, right);
    mem = coalesse(left, next_and_free);
  } else if (get_state(left) == UNALLOCATED) {
    printf("left is unallocated\n");
    mem = coalesse(left, mem);
  } else if (get_state(right) == UNALLOCATED) {
    printf("right is unallocated\n");
    mem = coalesse(mem, right);
  } else {
    printf("neither were unallocated\n");
  } */
  
  insert_fenceposts(mem, size);
  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);

  if (lastFencePost != NULL) {
    header *oldFencePost = get_left_header(get_left_header(hdr));
    if (oldFencePost == lastFencePost) {
      header *prev = get_left_header(hdr);
      prev = coalesse(lastFencePost, prev);
      mem = coalesse(prev, mem);
      lastfence = true;
    }
  }
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  if (lastfence) {
    lastFencePost = get_right_header(hdr);
  }

  return hdr;
}

/**
 * @brief Helper to find a block of the right size in the free list
 *
 * @param actual_size
 *
 * @return a pointer to the block in the free list
*/
header * find_free(size_t actual_size) { // actual_size does not include the header. see if we need to add the header size to actualsize
  header *p = NULL;
  header *next = NULL;
  int i = actual_size / 8;
  for (i; i < N_LISTS; i++) {
    p = &freelistSentinels[i];
    next = p->next;
    if (next != p && p->size_state > actual_size) {
      return p;
    }
  }
  return NULL;
}


/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
  // TODO implement allocation
  if (raw_size == 0) {
    return NULL;
  }

  //make sure we are allocating enough bytes
  size_t round_s = ((raw_size + 7) / 8) * 8;
  if (round_s < ALLOC_HEADER_SIZE) {
    round_s = ALLOC_HEADER_SIZE;
  }

  int list_num = round_s / 8 - 1;
  if (list_num >= N_LISTS) {
    list_num = N_LISTS - 1;
  }

  size_t total_size = round_s + ALLOC_HEADER_SIZE;

  int i = list_num;
  header * p = NULL;
  for (i; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist != freelist->next) {
      p = freelist->next;
      break;
    }
  }
  header *new = NULL;

  //if this is the last list we need to find a different obj
  if (p == NULL || get_size(p) < total_size) {
    p = allocate_chunk(ARENA_SIZE);
    if (p == NULL) {
      errno = ENOMEM;
      return NULL;
    }
    p = add_to_free_list(p);

    header * prevFencePost = get_header_from_offset(p, -ALLOC_HEADER_SIZE);
    insert_os_chunk(prevFencePost);

    if (p == NULL) {
      errno = ENOMEM;
      return NULL;
    }

  }

  if (p != NULL && get_size(p) >= total_size) {
    size_t extra_size = get_size(p) - total_size;
    //case 1, the block is exactly the correct size
    if (get_size(p) == total_size || extra_size < sizeof(header)) {
      new = p;
      remove_from_freelist(p, list_num);
    //TODO: case 2 the block is bigger, but cannot be split //might not work
    //case 3, the block is bigger and can be split
    } else {
      new = get_header_from_offset(p, extra_size);
      set_size(new, total_size);
      new->left_size = extra_size;
      set_size(p, extra_size);
    }
    set_state(new, ALLOCATED);

    //update the pointer to the right's left size attribute
    get_header_from_offset(new, total_size)->left_size = total_size;
  }
  return (header *) new->data;
}

/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE); //sizeof(header));
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
  // TODO implement deallocation
  header *free = ptr_to_header(p);

  //TODO check if there are other cases in which we cannot free
  if (p == NULL) {
    return;
  }
  header *check_next = get_right_header(free);
  header *check_prev = get_left_header(free);
  header *final = NULL;

  //call coalesse with next and previous if those blocks are free
  if (get_state(check_next) == UNALLOCATED && get_state(check_prev) == UNALLOCATED) {
    header *next_and_free = coalesse(free, check_next);
    final = coalesse(check_prev, next_and_free);
  } else if (get_state(check_prev) == UNALLOCATED) {
    final = coalesse(check_prev, free);
  } else if (get_state(check_next) == UNALLOCATED) {
    final = coalesse(free, check_next);
  } else {
    final = add_to_free_list(free);
  }
  
  //TODO set the values of final (size, state, left and right pointers)
  set_state(final, UNALLOCATED);

  // set the left_size pointer for the pointer after the free block


}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist;
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        printf("cycle in list %d\n\n\n", i);
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_header_from_offset(block, get_size(block));

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void basic_print(header * block) {
	printf("[%zd] -> ", get_size(block));
}

/**
 * @brief Print just the block's size
 *
 * @param block The block to print
 */
void print_list(header * block) {
	printf("[%zd]\n", get_size(block));
}

/**
 * @brief return a string representing the allocation status
 *
 * @param allocated The allocation status field
 *
 * @return A string representing the allocation status
 */
static inline const char * allocated_to_string(char allocated) {
  switch(allocated) {
    case UNALLOCATED: 
      return "false";
    case ALLOCATED:
      return "true";
    case FENCEPOST:
      return "fencepost";
  }
  assert(false);
}

static bool check_color() {
  if (!check_env) {
    // genenv allows accessing environment varibles
    const char * var = getenv(MALLOC_COLOR);
    use_color = var != NULL && !strcmp(var, "1337_CoLoRs");
    check_env = true;
  }
  return use_color;
}

/**
 * @brief Change the tty color based on the block's allocation status
 *
 * @param block The block to print the allocation status of
 */
static void print_color(header * block) {
  if (!check_color()) {
    return;
  }

  switch(get_state(block)) {
    case UNALLOCATED:
      printf("\033[0;32m");
      break;
    case ALLOCATED:
      printf("\033[0;34m");
      break;
    case FENCEPOST:
      printf("\033[0;33m");
      break;
  }
}

static void clear_color() {
  if (check_color()) {
    printf("\033[0;0m");
  }
}

static inline bool is_sentinel(void * p) {
  for (int i = 0; i < N_LISTS; i++) {
    if (&freelistSentinels[i] == p) {
      return true;
    }
  }
  return false;
}

/**
 * @brief Print the free list pointers if RELATIVE_POINTERS is set to true
 * then print the pointers as an offset from the base of the heap. This allows
 * for determinism in testing. 
 * (due to ASLR https://en.wikipedia.org/wiki/Address_space_layout_randomization#Linux)
 *
 * @param p The pointer to print
 */
void print_pointer(void * p) {
  if (is_sentinel(p)) {
    printf("SENTINEL");
  } else {
    if (RELATIVE_POINTERS) {
      printf("%04zd", p - base);
    } else {
      printf("%p", p);
    }
  }
}

/**
 * @brief Verbose printing of all of the metadata fields of each block
 *
 * @param block The block to print
 */
void print_object(header * block) {
  print_color(block);

  printf("[\n");
  printf("\taddr: ");
  print_pointer(block);
  puts("");
  printf("\tsize: %zd\n", get_size(block) );
  printf("\tleft_size: %zd\n", block->left_size);
  printf("\tallocated: %s\n", allocated_to_string(get_state(block)));
  if (!get_state(block)) {
    printf("\tprev: ");
    print_pointer(block->prev);
    puts("");

    printf("\tnext: ");
    print_pointer(block->next);
    puts("");
  }
  printf("]\n");

  clear_color();
}

/**
 * @brief Simple printer that just prints the allocation status of each block
 *
 * @param block The block to print
 */
void print_status(header * block) {
  print_color(block);
  switch(get_state(block)) {
    case UNALLOCATED:
      printf("[U]");
      break;
    case ALLOCATED:
      printf("[A]");
      break;
    case FENCEPOST:
      printf("[F]");
      break;
  }
  clear_color();
}

/*
static void print_bitmap() {
  printf("bitmap: [");
  for(int i = 0; i < N_LISTS; i++) {
    if ((freelist_bitmap[i >> 3] >> (i & 7)) & 1) {
      printf("\033[32m#\033[0m");
    } else {
      printf("\033[34m_\033[0m");
    }
    if (i % 8 == 7) {
      printf(" ");
    }
  }
  puts("]");
}
*/

/**
 * @brief Print a linked list between two nodes using a provided print function
 *
 * @param pf Function to perform the actual printing
 * @param start Node to start printing at
 * @param end Node to stop printing at
 */
void print_sublist(printFormatter pf, header * start, header * end) {  
  for (header * cur = start; cur != end; cur = cur->next) {
    pf(cur); 
  }
}

/**
 * @brief print the full freelist
 *
 * @param pf Function to perform the header printing
 */
void freelist_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    if (freelist->next != freelist) {
      printf("L%zu: ", i);
      print_sublist(pf, freelist->next, freelist);
      puts("");
    }
    fflush(stdout);
  }
}

/**
 * @brief print the boundary tags from each chunk from the OS
 *
 * @param pf Function to perform the header printing
 */
void tags_print(printFormatter pf) {
  if (!pf) {
    return;
  }

  for (size_t i = 0; i < numOsChunks; i++) {
    header * chunk = osChunkList[i];
    pf(chunk);
    for (chunk = get_right_header(chunk);
         get_state(chunk) != FENCEPOST; 
         chunk = get_right_header(chunk)) {
        pf(chunk);
    }
    pf(chunk);
    fflush(stdout);
  }
}
