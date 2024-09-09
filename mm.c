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

#include <math.h>

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {"jungle_9th", "SEONMI KIM", "dev.ddubbu@gmail.com", "", ""};

/* 상수 */
typedef enum { FREE = 0, ALLOCATED = 1 } BlockStatus;
#define ADDR_SIZE 4                // Word size (bytes) = Header, Footer block
#define DSIZE 8                    // Double word (bytes) = ALIGNMENT
#define ALIGNMENT 8                //
#define MIN_BLOCK_SIZE (DSIZE * 2) // Minimum block size or length 8(header + footer) + 8(payload has prev, next)
#define CHUNKSIZE (1 << 12)        // (=4096) Extend heap by this amount (bytes)
#define FINAL_BLOCK_SIZE (ADDR_SIZE * 4)
#define IDX_LIST_CNT 14
#define IDX_LIST_BLK_SIZE (IDX_LIST_CNT + 4)

/* 매크로 */
#define MAX(x, y) (x > y ? x : y)                //
#define MIN(x, y) (x < y ? x : y)                //
#define PUT(p, val) (*(unsigned int *)(p) = val) //
#define GET(p) (*(unsigned int *)(p))            // read a word(4bytes, size of int) at address p

#define PACK(size, allocated) ((size) | (allocated)) // 상위 : block size | 하위 : 할당 비트 (BlockStatus)

/**
 * Read the size and allocated fields from address p
 * ref. [fig 9.39] heap memory block format
 * ~0x7 = ~(0000 0111) = 1111 1000
 * 0x1 = (0000 0001)
 */
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1)) // GET(HDRP(p)) 일반화할 수 없는 exclude_free_block이유? FTR에서 읽어올 수 있음
#define GET_ALLOC(p) (GET(p) & 0x1)

/**
 * Given block ptr bp, compute address of its header and footer
 * heap memory block: [header(word) | data | footer (word)]
 * bp: 메모리 블록의 데이터 영역을 가리키는 포인터
 * (char *): 1바이트 단위로 포인터 연산이 가능함
 * GET_SIZE(HDRP(bp)): 블록 전체 크기
 */
#define HDRP(bp) ((char *)(bp) - ADDR_SIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * ADDR_SIZE)
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - 2 * ADDR_SIZE))) // prev_ftrp에서 size 얻기

#define BLK_PTR(p) (*(void **)(p))
#define NEXT_FREEP(bp) (BLK_PTR(bp))

static int find_start_idx(size_t size);
static void **find_start_bpp(size_t size);
static void *extend_heap(size_t words);
static void exclude_free_block(void **bpp);
static void set_block(void *, size_t, BlockStatus);

/*
 * mm_init - initialize the malloc package.
 */

char *index_list_p;
int mm_init(void) {
    void *heap_listp;

    if ((heap_listp = mem_sbrk((IDX_LIST_BLK_SIZE)*ADDR_SIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp + 0, PACK(0, ALLOCATED));                                           // start(Alignment padding) - Q. root 생기면서 양끝 padding 제거해도 될거 같은데
    PUT(heap_listp + (1 * ADDR_SIZE), PACK(IDX_LIST_BLK_SIZE * ADDR_SIZE, ALLOCATED)); // index list header
    for (int i = 2; i < 2 + IDX_LIST_CNT; i++) {
        /**
         * size classes
         * 2^0 {1}
         * 2^1 {2}
         * 2^2 {3, 4}
         * ...
         * 2^12 {... , 4096}
         * 2^13 {4097, inf}
         */
        PUT(heap_listp + (i * ADDR_SIZE), NULL);
    }
    PUT(heap_listp + ((2 + IDX_LIST_CNT) * ADDR_SIZE), PACK(IDX_LIST_BLK_SIZE * ADDR_SIZE, ALLOCATED)); // index list footer
    PUT(heap_listp + ((3 + IDX_LIST_CNT) * ADDR_SIZE), PACK(0, ALLOCATED));                             // end(가장자리 조건 제거)
    index_list_p = heap_listp + 2 * ADDR_SIZE;

    return 0;
}

/* mm_free - Freeing a block does nothing. */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    set_block(bp, size, FREE);

    // TODO: add_insert_free_list
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;
    size_t extend_heap_size;
    char *bp;

    if (size <= 0)
        return NULL;

    size_t header_n_footer_size = 2 * ADDR_SIZE;

    /**
     * Adjust block size to include overhead and alignment reqs.
     * 최소 16바이트 크기의 블록 구성
     * */
    if (size <= DSIZE)
        asize = MIN_BLOCK_SIZE; // header_n_footer_size + DSIZE
    else
        /**
         * 1. (size + (헤더와 푸터 크기) + (정렬 맞추기 보정))
         * 2. asize / DSIZE = 필요한 블록 크기 계산
         * 3. asize * DSIZE = 실제 메모리 블록 크기 결정
         * */
        asize = DSIZE * ((size + (header_n_footer_size) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */

    void **bpp = find_start_bpp(size);
    if ((bp = BLK_PTR(bpp)) != NULL) {
        exclude_free_block(bpp);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    int idx = find_start_idx(size);
    extend_heap_size = 1 << idx;
    if ((bp = extend_heap(extend_heap_size / ADDR_SIZE)) == NULL)
        // free_list 연결 불필요, 추후 free 시 연결해주면 됨
        return NULL;

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

    size_t copy_size = MIN(size, GET_SIZE(HDRP(ptr)));
    memcpy(newptr, ptr, copy_size);
    mm_free(ptr);
    return newptr;
}

/* ==================== Utility ==================== */

static int find_start_idx(size_t size) {
    if (size > 2 << (IDX_LIST_CNT - 2)) {
        return IDX_LIST_CNT - 1;
    }

    return (int)ceil(log2(size));
}

static void **find_start_bpp(size_t size) {
    int idx = find_start_idx(size);
    return index_list_p + idx * ADDR_SIZE;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * ADDR_SIZE : words * ADDR_SIZE; // 더블 워드 정렬 유지
    if ((long)(bp = mem_sbrk(size)) == -1)                                   // 힙 확장
        return NULL;

    set_block(bp, size, FREE);
    return bp;
}

static void exclude_free_block(void **bpp) { BLK_PTR(bpp) = NEXT_FREEP(bpp); }

static void set_block(void *bp, size_t size, BlockStatus alloced) {
    PUT(HDRP(bp), PACK(size, alloced));
    PUT(FTRP(bp), PACK(size, alloced));
}