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

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static void* first_block;

static void* find_fit(size_t size, int type);
static void* extend_heap(size_t size);
static void  merge(void* p1, void* p2);
static void* coalesce(void* ptr);
static void place(void* ptr, size_t size);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    void *start = mem_sbrk(4 * WSIZE);
    if (start == (void *)-1) {
        return -1;
    }
    PUT(start, 0);
    PUT(((char *)start) + 1 * WSIZE, PACK(DSIZE, 1));
    PUT(((char *)start) + 2 * WSIZE, PACK(DSIZE, 1));
    PUT(((char *)start) + 3 * WSIZE, PACK(0, 1));
    first_block = extend_heap(CHUNKSIZE / WSIZE);
    if (first_block == (void *)0) return -1;
    return 0;
}

static void *find_first_fit(size_t size) {
    void *i;
    for (i = first_block; GET_SIZE(HDRP(i)) > 0; i = NEXT_BLKP(i)) {
        if (GET_ALLOC(HDRP(i))) continue;
        if (GET_SIZE(HDRP(i)) >= size) break;
    }
    return i;
}

static void *find_fit(size_t size, int type) {
    switch(type) {
        case 0:
            return find_first_fit(size);
    }
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// size bytes payload
void *mm_malloc(size_t size)
{
    // at least 16B
    if (size <= DSIZE)
        size = 2 * DSIZE;
    else 
        size = ALIGN(size + DSIZE);
    void *i = find_fit(size, 0);
    if (GET_SIZE(HDRP(i)) == 0) {
        i = extend_heap(MAX(size, CHUNKSIZE) / WSIZE);
        if (i == (void *)0) return i;
    }
    place(i, size);
    return i;
}
static void place(void* ptr, size_t size) {
    size_t osize = GET_SIZE(HDRP(ptr));
    if (osize - size < 2 * DSIZE) {
        PUT(HDRP(ptr), PACK(osize, 1));
        PUT(FTRP(ptr), PACK(osize, 1));
        return;
    }
    PUT(HDRP(ptr), PACK(size, 1));
    PUT(FTRP(ptr), PACK(size, 1));
    ptr = NEXT_BLKP(ptr);
    PUT(HDRP(ptr), PACK(osize - size, 0));
    PUT(FTRP(ptr), PACK(osize - size, 0));
}

// return the data pointer of the new block
static void* extend_heap(size_t words) {
    if (words & 0x1) words++;
    size_t bytes = words * WSIZE;
    void *old = mem_sbrk(bytes);
    if (old == (void *)-1) return 0;
    PUT(HDRP(old), PACK(bytes, 0));
    PUT(FTRP(old), PACK(bytes, 0));
    PUT(HDRP(NEXT_BLKP(old)), PACK(0, 1));
    return coalesce(old);
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    if (ptr <= mem_heap_lo() || ptr >= mem_heap_hi()) return;
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

// p1 is near to p2
static void merge(void* p1, void* p2) {
    if (NEXT_BLKP(p1) != p2) return;
    int alloc1 = GET_ALLOC(HDRP(p1)), alloc2 = GET_ALLOC(HDRP(p2));
    // printf("alloc1: %d, alloc2: %d\n", alloc1, alloc2);
    if (alloc1 || alloc2) return;
    size_t s1 = GET_SIZE(HDRP(p1)), s2 = GET_SIZE(HDRP(p2));
    // printf("merge: p1 header : %p, p1 footer: %p, p2 header: %p, p2 footer: %p, highest: %p\n", 
    // HDRP(p1), FTRP(p1), HDRP(p2), FTRP(p2), mem_heap_hi());
    PUT(HDRP(p1), PACK(s1 + s2, 0));
    PUT(FTRP(p1), PACK(s1 + s2, 0));
}

static void* coalesce(void *ptr) {
    if (GET_ALLOC(HDRP(ptr))) return ptr;
    void *pre = PREV_BLKP(ptr);
    int pre_alloc = GET_ALLOC(HDRP(pre));
    if (!pre_alloc) {
        merge(pre, ptr);
        ptr = pre;
    }
    void *next = NEXT_BLKP(ptr);
    int next_alloc = GET_ALLOC(HDRP(next));
    if (!next_alloc) {
        merge(ptr, next);
    }
    return ptr;
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
    void *newptr = mm_malloc(size);
    if (newptr == NULL) return NULL;
    size_t osize = GET_SIZE(HDRP(ptr));
    if (size < osize)
      osize = size;
    memcpy(newptr, ptr, osize);
    mm_free(ptr);
    return newptr;
}


