/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1<<12)   /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp, compute address of next and previous blocks */
#define GET_PRED(bp)  ((void *)GET(bp))
#define PUT_PRED(bp, pred) ((*(unsigned int *)(bp)) = (pred))
#define GET_SUCC(bp)  ((void *)GET(((char *)bp + WSIZE)))
#define PUT_SUCC(bp, succ) (*((unsigned int *)((char *)(bp) + WSIZE)) = (succ))

#define LIST_COUNT 29
#define INT_MAX 0x7fffffff
static int threshold[LIST_COUNT] = {
    0x10, 0x20, 0x40, 0x80,
    0x100, 0x200, 0x400, 0x800,
    0x1000, 0x2000, 0x4000, 0x8000,
    0x10000, 0x20000, 0x40000, 0x80000,
    0x100000, 0x200000, 0x400000, 0x800000,
    0x1000000, 0x2000000, 0x4000000, 0x8000000,
    0x10000000, 0x20000000, 0x40000000, 0x80000000,
    INT_MAX};
inline int get_index(int size) {
    for (int i = 0; i < LIST_COUNT; i++) {
        if (size < threshold[i]) return i;
    }
    return LIST_COUNT - 1;
}


static void* list_head[LIST_COUNT + 1];
static void* list_tail[LIST_COUNT + 1];
static void* extend_heap(size_t size);
static void* coalesce(void *ptr);

static void link_node(void* bp1, void* bp2) {
    PUT_SUCC(bp1, bp2);
    PUT_PRED(bp2, bp1);
}

// only when coalesce we pop a node by pointer
// bp must not be list_head or list_tail
inline static void pop(void* bp) {
    link_node(GET_PRED(bp), GET_SUCC(bp));
}

inline static void* pop_front(int i) {
    void* head = GET_SUCC(list_head[i]);
    if (head == list_tail[i]) return NULL;
    pop(head);
    return head;
}

inline static void push_back(void* bp) {
    int i = get_index(GET_SIZE(HDRP(bp)));
    void* pred = GET_PRED(list_tail[i]);
    link_node(pred, bp);
    link_node(bp, list_tail[i]);
}

inline static void push_front(void* bp) {
    int i = get_index(GET_SIZE(HDRP(bp)));
    void* old_head = GET_SUCC(list_head[i]);
    link_node(list_head[i], bp);
    link_node(bp, old_head);
}

static void print_usage() {
    int unused = 0;
    for (int j = 0; j < LIST_COUNT; j++) {
        for (void* i = GET_SUCC(list_head[j]); i != list_tail[j]; i = GET_SUCC(i)) {
            unused += GET_SIZE(HDRP(i));
        }
    }
    
    int hsize = mem_heapsize() - WSIZE + 2 * (2 * DSIZE);
    printf("heap size: %d, unused: %d\n", hsize, unused);
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void* start = mem_sbrk(WSIZE + LIST_COUNT * 2 * (2 * DSIZE) + WSIZE);
    // set start block
    PUT(start, PACK(0, 0)); // to align payload address
    list_head[0] = (void *)((char *)start + DSIZE);
    for (int i = 0; i < LIST_COUNT; i++) {
        PUT(HDRP(list_head[i]), PACK(2 * DSIZE, 1));
        PUT(FTRP(list_head[i]), PACK(2 * DSIZE, 1));
        
        list_tail[i] = NEXT_BLKP(list_head[i]);
        PUT(HDRP(list_tail[i]), PACK(2 * DSIZE, 1));
        PUT(FTRP(list_tail[i]), PACK(2 * DSIZE, 1));
        
        // link head and tail
        link_node(list_head[i], list_tail[i]);
        list_head[i + 1] = NEXT_BLKP(list_tail[i]);
    }
    // set end block
    void* end = NEXT_BLKP(list_tail[LIST_COUNT - 1]); // avoid to being out of heap
    PUT(HDRP(end), PACK(0, 0));
    return 0;
}

static void* extend_heap(size_t words) {
    if (words % 2) words++;
    size_t bytes = words * WSIZE;
    void* old = mem_sbrk(bytes);
    if (old == (void *) -1) {
        return old;
    }
    PUT(HDRP(old), PACK(bytes, 0));
    PUT(FTRP(old), PACK(bytes, 0));
    // set end block
    void* end = NEXT_BLKP(old);
    PUT(HDRP(end), PACK(0, 0));
    return old;
}

// p1 is near to p2
// p1 and p2 is already in free list
static void merge(void* p1, void* p2) {
    if (NEXT_BLKP(p1) != p2) return;
    int alloc1 = GET_ALLOC(HDRP(p1)), alloc2 = GET_ALLOC(HDRP(p2));
    if (alloc1 || alloc2) return;
    int s1 = GET_SIZE(HDRP(p1)), s2 = GET_SIZE(HDRP(p2));
    int s = s1 + s2;
    int i1 = get_index(s1), i2 = get_index(s2);
    PUT(HDRP(p1), PACK(s, 0));
    PUT(FTRP(p1), PACK(s, 0));
    pop(p2);
    if (s >= threshold[i1]) {
        pop(p1);
        push_back(p1);
    }
}

static void* coalesce(void *ptr) {
    int i = get_index(GET_SIZE(HDRP(ptr)));
    int head = HDRP(ptr);
    int alloc = GET_ALLOC(head);
    if (GET_ALLOC(HDRP(ptr))) {
        return ptr;
    }
    void *pre = PREV_BLKP(ptr);
    int pre_alloc = GET_ALLOC(HDRP(pre));
    if (!pre_alloc) {
        merge(pre, ptr);
        ptr = pre;
    }
    void *next = NEXT_BLKP(ptr);
    if (GET_SIZE(HDRP(next)) == 0) // no next block exists
        return ptr;
    int next_alloc = GET_ALLOC(HDRP(next));
    if (!next_alloc) {
        merge(ptr, next);
    }
    return ptr;
}

static void* coalesce_list(int i) {
    void* succ;
    void* pred = list_head[i];
    void* j = GET_SUCC(list_head[i]);
    while (j != list_tail[i]) {
        void* p = coalesce(j);
        if (p != j) {
            j = GET_SUCC(pred);
            continue;
        }
        int loc = get_index(GET_SIZE(HDRP(j)));
        if (loc == i) {
            pred = j;
            j = GET_SUCC(j);
        } else {
            j = GET_SUCC(pred);
        }
    }
}

static void *find_first_fit(size_t size) {
    for (int i = get_index(size); i < LIST_COUNT; i++) {
        for (void *j = GET_SUCC(list_head[i]); j != list_tail[i]; j = GET_SUCC(j)) {
            if (GET_SIZE(HDRP(j)) >= size) return j;
        }
    }
    return NULL;
}

static void *find_fit(size_t size, int type) {
    void* i;
    switch(type) {
        case 0:
            i = find_first_fit(size);
            break;
    }
    if (i == NULL) {
        /* merge */
        // for (int j = get_index(size); j >= 0; j--) {
        //     coalesce_list(j);
        // }
        return NULL;
    }
    pop(i);
    return i;
}

static void place(void* ptr, size_t size) {
    size_t block_size = GET_SIZE(HDRP(ptr));
    if (block_size - size < 2 * DSIZE) {
        PUT(HDRP(ptr), PACK(block_size, 1));
        PUT(FTRP(ptr), PACK(block_size, 1));
        return;
    }
    PUT(HDRP(ptr), PACK(size, 1));
    PUT(FTRP(ptr), PACK(size, 1));
    ptr = NEXT_BLKP(ptr);
    PUT(HDRP(ptr), PACK(block_size - size, 0));
    PUT(FTRP(ptr), PACK(block_size - size, 0));
    push_back(ptr);
    coalesce(ptr);
}


/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size = ALIGN(size);
    size_t nsize = MAX(size, DSIZE) + DSIZE;
    void* block = NULL;
    for (int i = 0; i < 2 && (block == NULL); i++) {
        block = find_fit(nsize, 0); 
    }
    if (block != NULL) {
        place(block, nsize);
        return block;
    }
    block = extend_heap(nsize / WSIZE);
    if (block == (void *) -1) {
        return NULL;
    }
    place(block, GET_SIZE(HDRP(block)));
    return block;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr < mem_heap_lo() || ptr > mem_heap_hi() || GET_ALLOC(HDRP(ptr)) == 0) 
        return;
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    push_back(ptr);
    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL) return mm_malloc(size);
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }
    if (GET_ALLOC(HDRP(ptr)) == 0) return NULL;
    size = MAX(ALIGN(size), DSIZE) + DSIZE;
    size_t osize = GET_SIZE(HDRP(ptr));
    if (osize >= size) {
        place(ptr, size);
        return ptr;
    }
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    memcpy(newptr, ptr, osize);
    mm_free(ptr);
    return newptr;
}














