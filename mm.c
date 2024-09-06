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
#include "mm.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {"jungle_9th", "SEONMI KIM", "dev.ddubbu@gmail.com", "", ""};

/* 상수 */
typedef enum { FREE = 0, ALLOCATED = 1 } BlockStatus;
#define WSIZE 4                    // Word size (bytes) = header/footer of block size
#define DSIZE 8                    // Double word (bytes) = ALIGNMENT
#define CHUNKSIZE (1 << 12)        // (=4096) Extend heap by this amount (bytes)
#define ALIGNMENT 8                //
#define MIN_BLOCK_SIZE (DSIZE * 2) //  Minimum block size (header + footer)

/* 매크로 */
#define MAX(x, y) (x > y ? x : y)                    //
#define MIN(x, y) (x < y ? x : y)                    //
#define PUT(p, val) (*(unsigned int *)(p) = val)     //
#define GET(p) (*(unsigned int *)(p))                // read a word(4bytes, size of int) at address p
#define PACK(size, allocated) ((size) | (allocated)) // 상위 : size | 하위 : 할당 비트 (BlockStatus)

/**
 * Read the size and allocated fields from address p
 * ref. [fig 9.39] heap memory block format
 * ~0x7 = ~(0000 0111) = 1111 1000
 * 0x1 = (0000 0001)
 */
#define GET_SIZE(p) (GET(p) & ~0x7) // GET(HDRP(p)) 일반화할 수 없는 이유? FTR에서 읽어올 수 있음
#define GET_ALLOC(p) (GET(p) & 0x1)

/**
 * rounds up to the nearest multiple of ALIGNMENT
 * ALIGNMENT 8이므로, 메모리 주소가 8의 배수가 되어야함 (더 빠르게 처리 가능)
 * Q. 8바이트 정렬
 * - (Yes) : 유지
 * - (No) : 7만큼 더한 후, & ~0x7 (=1000) 비트 연산 => 하위 3비트를 0으로 맞추기
 * */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/**
 * Given block ptr bp, compute address of its header and footer
 * heap memory block: [header(word) | data | footer (word)]
 * bp: 메모리 블록의 데이터 영역을 가리키는 포인터
 * (char *): 1바이트 단위로 포인터 연산이 가능함
 * GET_SIZE(HDRP(bp)): 블록 전체 크기
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * WSIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - 2 * WSIZE))) // prev_ftrp에서 size 얻기

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_first_fit(size_t asize);
static void place(void *bp, size_t size);
static void set_block(void *, size_t, BlockStatus);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {
    void *heap_listp;
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                                    // Alignment padding
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, ALLOCATED)); // P.H
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, ALLOCATED)); // P.F
    PUT(heap_listp + (3 * WSIZE), PACK(0, ALLOCATED));     // E.H
    heap_listp += DSIZE;                                   // 실제 데이터 영역이 시작되는 (P.F 뒤의 위치)로 이동

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;

    return 0;
}

/* mm_free - Freeing a block does nothing. */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    set_block(bp, size, FREE);
    coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL;

    /**
     * Adjust block size to include overhead and alignment reqs.
     * 최소 16바이트 크기의 블록 구성
     * */
    if (size <= DSIZE)
        asize = MIN_BLOCK_SIZE;
    else
        /**
         * 1. (size + (헤더와 푸터 크기) + (정렬 맞추기 보정))
         * 2. asize / DSIZE = 필요한 블록 크기 계산
         * 3. asize * DSIZE = 실제 메모리 블록 크기 결정
         * */
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_first_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;

    place(bp, asize);
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
    if (ptr == NULL)
        return mm_malloc(size);

    if (size <= 0) {
        mm_free(ptr);
        return NULL;
    }

    void *newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    size_t copy_data_size = MIN(size, GET_SIZE(HDRP(ptr)) - 2 * WSIZE);
    memcpy(newptr, ptr, copy_data_size);
    mm_free(ptr);
    return newptr;
}

/* ==================== Utility ==================== */

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 더블 워드 정렬 유지
    if ((long)(bp = mem_sbrk(size)) == -1)                           // 힙 확장
        return NULL;

    set_block(bp, size, FREE);
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        /* Case 1 : same as */
        return bp;
    } else if (prev_alloc && !next_alloc) {
        /**
         * Case 2 : new block
         * - header : bp
         * - footer : bp Q. FTRP(NEXT_BLKP(bp)) 로 바뀌어야하는거 아닌가?
         * */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, FREE));
        PUT(FTRP(bp), PACK(size, FREE));
    } else if (!prev_alloc && next_alloc) {
        /**
         * Case 3 : new block
         * - header : HDRP(PREV_BLKP(bp)
         * - footer : FTRP(bp)
         * */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, FREE));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
    } else {
        /**
         * Case 4 : new block
         * - header : HDRP(PREV_BLKP(bp))
         * - footer : FTRP(NEXT_BLKP(bp))
         * */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));
        bp = PREV_BLKP(bp);
    }

    return bp;
}

static void *find_first_fit(size_t asize) {
    void *bp = mem_heap_lo() + 2 * WSIZE;
    size_t size;

    while (GET_SIZE(HDRP(bp)) > 0) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
            return bp;
        bp = NEXT_BLKP(bp);
    }

    return NULL; // No Fit.
}

/**
 * 가용 블록의 시작 부분에 배치 후
 * 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 경우에만 분할
 * */
static void place(void *bp, size_t asize) {
    size_t cur_size = GET_SIZE(HDRP(bp));
    set_block(bp, asize, ALLOCATED);
    if ((cur_size - asize) >= MIN_BLOCK_SIZE) {
        set_block(bp, asize, ALLOCATED);
        set_block(NEXT_BLKP(bp), cur_size - asize, FREE);
    } else {
        set_block(bp, cur_size, ALLOCATED);
    }
}

static void set_block(void *bp, size_t size, BlockStatus alloced) {
    PUT(HDRP(bp), PACK(size, alloced));
    PUT(FTRP(bp), PACK(size, alloced));
}