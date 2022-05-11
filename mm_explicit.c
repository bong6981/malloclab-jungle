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
    "Jungle",
    /* First member's full name */
    "Bong6981",
    /* First member's email address */
    "bong6981@gihub.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double Word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend Heap by this amount (bytes) */
#define MINBLOCKSIZE 16     /* Minimum size for a free block, 
                               includes 4 bytes for header, footer, two pointers to the prev and the next free block */ 
#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr pb, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE((char *)(bp)-WSIZE))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE((char *)(bp)-DSIZE))

#define PREV_FRBLKP(bp) (*(char **)(bp))
#define NEXT_FRBLKP(bp) (*(char **)(bp+WSIZE))

static char *heap_listp;
static char *free_listp;

static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static void insert_free_block();
static void remove_free_block(void *bp);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap. */
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(2 * WSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(2 * WSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));         /* Epilogue header */
    heap_listp += (2 * WSIZE);                         /* 포인터를 Prolouge 헤더 바로 다음으로 옮긴다 */
    free_listp = heap_listp;
    if (extend_heap(4) == NULL){ 
        return -1;
    }
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL) /* 최대 할당 크기를 넘었을 때 */
        return -1;
  
    return 0;
}


static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignmnet */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         /* Free block header  */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer  */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /*Coalesce if the previous block was free */
    return coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); 

    size_t size = GET_SIZE(HDRP(bp));

    /* If the previous block is free, then coalesce the current block (bp) and the previous block */
    if (!prev_alloc && next_alloc) { /* Case 2 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        remove_free_block(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (prev_alloc && !next_alloc){ /* Case 3 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc){ /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)))
              + GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }
    /* case 1  : insert into free blocks*/
    insert_free_block(bp);
    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignmnet reqs. */
    if (size < DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) 
        return NULL;
    place(bp, asize);
    return bp;
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp;

    for (bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = NEXT_FRBLKP(bp))
    {
        if (asize <= GET_SIZE(HDRP(bp)))
            return bp;
    }
    return NULL;
}

static void place(void *bp, size_t asize)
{

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) < WSIZE * 4)
    { /* 블록 크키가 작아 다른 블록 할당할 수 없을 때(not split) */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        remove_free_block(bp);
    }
    else
    { /* 블록 크기가 다른 블록을 할당할 수 있을 만큼 클 때(split) */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        remove_free_block(bp);

        csize -= asize;
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize, 0));
        PUT(FTRP(bp), PACK(csize, 0));
        coalesce(bp);
    }
}

static void insert_free_block(void *bp)
{   
    NEXT_FRBLKP(bp) = free_listp;
    PREV_FRBLKP(free_listp) = bp;
    PREV_FRBLKP(bp) = NULL;
    free_listp = bp;
}


static void remove_free_block(void *bp)
{
	if(PREV_FRBLKP(bp))
        NEXT_FRBLKP(PREV_FRBLKP(bp)) = NEXT_FRBLKP(bp);
    else
        free_listp = NEXT_FRBLKP(bp);
    PREV_FRBLKP(NEXT_FRBLKP(bp)) = PREV_FRBLKP(bp);
}


void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{   
    if ((int)size < 0) {
        return NULL;
    }

    if ((int)size == 0) {
        mm_free(bp);
        return NULL;
    }

    size_t allocated_size = GET_SIZE(HDRP(bp));
    size = size + (2 * WSIZE);

    // 이거 만약 split 하면 어떻게  어떻게 될까
    if (size <= allocated_size) {
        return bp;
    }

    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t csize;
    if (!next_alloc && (csize = allocated_size + GET_SIZE(HDRP(NEXT_BLKP(bp)))) >= size) {
        remove_free_block(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        return bp;
    }

    void *new_bp = mm_malloc(size);
    place(new_bp, size);
    memcpy(new_bp, bp, size);
    mm_free(bp);
    return new_bp;
}
