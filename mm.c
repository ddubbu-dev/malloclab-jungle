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

/*
TODO: 고민사항 2개 추가 필요
- free 할때 무한대 사이즈 어떻게?
- 무한대 사이즈 free 할때 어느 index로? header 필요한거 아님?
*/

/* 상수 */
typedef enum { FREE = 0, ALLOCATED = 1 } BlockStatus;
#define ADDR_SIZE 4         // Word size (bytes) = Header, Footer block
#define DSIZE 8             // Double word (bytes) = ALIGNMENT
#define ALIGNMENT 8         //
#define CHUNKSIZE (1 << 12) // (=4096) Extend heap by this amount (bytes)
#define FINAL_BLOCK_SIZE (ADDR_SIZE * 4)
#define IDX_LIST_CNT 22
#define MIN_SIZE_CLASS_IDX 3 // =8byte (ADDR_SIZE * 2) = (header, suc pointer)
// #define MAX_SIZE_CLASS_IDX 24      // =16MB
#define MAX_SIZE_CLASS_IDX 22      // =4MB
#define MIN_BLOCK_SIZE (DSIZE * 2) // TODO: MIN_SIZE_CLASS랑 정리 필요
#define IDX_LIST_BLK_SIZE (IDX_LIST_CNT + 2)

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
#define GET_SIZE(p) (GET(p) & ~(ALIGNMENT - 1))
#define GET_ALLOC(p) (GET(p) & 0x1)

#define HDRP(bp) ((char *)(bp) - ADDR_SIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * ADDR_SIZE)

#define BLK_PTR(p) (*(void **)(p))
#define NEXT_FREEP(bp) (BLK_PTR(bp + ADDR_SIZE))

static int find_size_class_idx(size_t size);
static void **find_start_bpp(size_t size);
static void *extend_heap(size_t words);
static void exclude_free_block(void **bpp);
static void set_block(void *, size_t, BlockStatus);
static void set_free_block(void *bp, size_t size, void *next_bp);

/*
 * mm_init - initialize the malloc package.
 */

char *index_list_p;
int mm_init(void) {
    void *heap_listp;

    if ((heap_listp = mem_sbrk(((IDX_LIST_BLK_SIZE + 2)) * ADDR_SIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp + 0, PACK(0, ALLOCATED));                                           // start(Alignment padding)
    PUT(heap_listp + (1 * ADDR_SIZE), PACK(IDX_LIST_BLK_SIZE * ADDR_SIZE, ALLOCATED)); // index list header
    for (int i = 2; i < 2 + IDX_LIST_CNT; i++) {
        /**
         * size classes
         * (0) 2^3 {8}
         * (1) 2^4 {16}
         * (2) 2^5 {32}
         * (3) 2^6 {64}
         * ...
         * (20) 2^23 {2^23}
         * (21) 2^24 {2^24}
         */
        PUT(heap_listp + (i * ADDR_SIZE), NULL);
    }
    PUT(heap_listp + ((2 + IDX_LIST_CNT) * ADDR_SIZE), PACK(IDX_LIST_BLK_SIZE * ADDR_SIZE, ALLOCATED)); // index list footer
    PUT(heap_listp + ((3 + IDX_LIST_CNT) * ADDR_SIZE), PACK(0, ALLOCATED));                             // end(가장자리 조건 제거)
    index_list_p = heap_listp + 2 * ADDR_SIZE;

    int extend_heap_size = 1 << MAX_SIZE_CLASS_IDX;
    void *bp;
    if ((bp = extend_heap(extend_heap_size / ADDR_SIZE)) == NULL)
        return NULL;

    void *bpp = find_start_bpp(extend_heap_size); // last size class idx
    BLK_PTR(bpp) = bp;

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
    int idx = find_size_class_idx(size);
    extend_heap_size = 1 << (idx + MIN_SIZE_CLASS_IDX);
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

static int find_size_class_idx(size_t size) {
    for (int i = MIN_SIZE_CLASS_IDX; i <= MAX_SIZE_CLASS_IDX; i++) {
        if (size <= (1 << i)) {
            return i - MIN_SIZE_CLASS_IDX;
        }
    }
}

static void **find_start_bpp(size_t size) {
    int idx = find_size_class_idx(size);
    return index_list_p + idx * ADDR_SIZE;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * ADDR_SIZE : words * ADDR_SIZE; // 더블 워드 정렬 유지
    if ((long)(bp = mem_sbrk(size)) == -1)                                   // 힙 확장
        return NULL;

    set_free_block(bp, size, NULL);
    return bp;
}

static void exclude_free_block(void **bpp) { BLK_PTR(bpp) = BLK_PTR(BLK_PTR(bpp)); }

static void set_block(void *bp, size_t size, BlockStatus alloced) {
    PUT(HDRP(bp), PACK(size, alloced));
    PUT(FTRP(bp), PACK(size, alloced));
}

static void set_free_block(void *bp, size_t size, void *next_bp) {
    PUT(HDRP(bp), size);
    NEXT_FREEP(bp) = next_bp;
}