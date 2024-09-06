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

/* Basic constants and macros */

#define FLAG_ALLOCATED 1 /* 할당됨 혹은 경계 블록의 사용 불가 상태 */
#define FLAG_FREE 0

#define WSIZE 4 /* Word and header/footer size (bytes) */
#define DSIZE 8 /* Double word size (bytes) = ALIGNMENT */
#define MIN_BLOCK_SIZE (DSIZE * 2)
#define CHUNKSIZE (1 << 12) /* (=4096) Extend heap by this amount (bytes) */

#define MAX(x, y) (x > y ? x : y)

/**
 * Pack a size and allocated bit into a word
 * 블록 크기 상위비트 | 할당 상태 하위 비트 (FLAG_ALLOCATED / FLAG_FREE)
 */
#define PACK(size, allocated) ((size) | (allocated))

/* Read and writed a word(4bytes, size of int) at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = val)

/**
 * Read the size and allocated fields from address p
 * ref. [fig 9.39] heap memory block format
 * ~0x7 = ~(0000 0111) = 1111 1000
 * 0x1 = (0000 0001)
 */
#define GET_SIZE(p) (GET(p) & ~0x7)  // TODO: HDRP 포함 로직으로 바뀌어야함
#define GET_ALLOC(p) (GET(p) & 0x1)

/**
 * Given block ptr bp, compute address of its header and footer
 * heap memory block: [header | data | footer]
 * bp: 메모리 블록의 데이터 영역을 가리키는 포인터
 * (char *): 1바이트 단위로 포인터 연산이 가능함
 * GET_SIZE(HDRP(bp)): 블록 전체 크기
 */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/**
 * Given block ptr bp, compute address of next and previous blocks
 * header, footer has same block size
 * */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))
// = #define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/**
 * rounds up to the nearest multiple of ALIGNMENT
 * ALIGNMENT 8 이므로, 메모리 주소가 8의 배수가 되어야함 (더 빠르게 처리 가능)
 * Q. 8바이트 정렬
 * - (Yes) : 유지
 * - (No) : 7만큼 더한 후, & ~0x7 (=1000) 비트 연산 => 하위 3비트를 0으로 맞추기
 * */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t size);
static void init_block(void *bp);  // TODO

/*
 * mm_init - initialize the malloc package.
 */
void *heap_listp;
int mm_init(void) {
  /* Create the initial empty heap */
  if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) return -1;

  PUT(heap_listp, 0); /* Alignment padding */
  /* Prologue, Epliogue : 힙 경계 식별을 위함 */
  PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, FLAG_ALLOCATED)); /* P.H */
  /* Q. 시작 주소 확인 필요 */
  PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, FLAG_ALLOCATED)); /* P.F */
  PUT(heap_listp + (3 * WSIZE), PACK(0, FLAG_ALLOCATED));     /* E.H */
  heap_listp += DSIZE; /* 실제 데이터 영역이 시작되는 (P.F 뒤의 위치)로 이동 */

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;

  return 0;
}

/* mm_free - Freeing a block does nothing. */
void mm_free(void *bp) {
  size_t size = GET_SIZE(HDRP(bp));

  PUT(HDRP(bp), PACK(size, FLAG_FREE));
  PUT(FTRP(bp), PACK(size, FLAG_FREE));
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
  if (size <= 0) return NULL;

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
  if ((bp = find_fit(asize)) != NULL) {
    place(bp, asize);
    return bp;
  }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize, CHUNKSIZE);
  if ((bp = extend_heap(extendsize / WSIZE)) == NULL) return NULL;

  place(bp, asize);
  return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) {
  void *oldptr = ptr;
  void *newptr;
  size_t copySize;

  newptr = mm_malloc(size);
  if (newptr == NULL) return NULL;
  copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
  if (size < copySize) copySize = size;
  memcpy(newptr, oldptr, copySize);  // Q. 어딨음?
  mm_free(oldptr);
  return newptr;
}

/* ==================== Utility ==================== */

static void *extend_heap(size_t words) {
  char *bp;
  size_t size;

  /* Allocate an even number of words to maintain alignment */
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
  if ((long)(bp = mem_sbrk(size)) == -1) return NULL;

  /* Initialize free block header/footer and the epilogue header */
  PUT(HDRP(bp), PACK(size, FLAG_FREE)); /* Free block header */
  PUT(FTRP(bp), PACK(size, FLAG_FREE)); /* Free block footer */
  PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

  /* Coalesce if the previous block was free */
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
    PUT(HDRP(bp), PACK(size, FLAG_FREE));
    PUT(FTRP(bp), PACK(size, FLAG_FREE));
  } else if (!prev_alloc && next_alloc) {
    /**
     * Case 3 : new block
     * - header : HDRP(PREV_BLKP(bp)
     * - footer : FTRP(bp)
     * */
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, FLAG_FREE));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, FLAG_FREE));
    bp = PREV_BLKP(bp);
  } else {
    /**
     * Case 4 : new block
     * - header : HDRP(PREV_BLKP(bp))
     * - footer : FTRP(NEXT_BLKP(bp))
     * */
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size, FLAG_FREE));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FLAG_FREE));
    bp = PREV_BLKP(bp);
  }

  return bp;
}

/* First Fit : heap_listp 처음부터 검색 후 크기가 맞는 첫 가용 블록 선택 */
static void *find_fit(size_t asize) {
  char *bp = heap_listp;

  while (1) {
    size_t size = GET_SIZE(HDRP(bp));
    int allocated = GET_ALLOC(bp);
    if (!allocated && size >= asize) return bp;
    bp = NEXT_BLKP(bp);
  }

  return NULL;  // no fit
}

/**
 * 가용 블록의 시작 부분에 배치 후
 * 나머지 부분의 크기가 최소 블록 크기와 같거나 큰 경우에만 분할 */
static void place(void *bp, size_t asize) {
  size_t cur_size = GET_SIZE(HDRP(bp));

  // Q. 경계 블록의 경우 사이즈가 DSIZE인지 WSIZE 인지..
  if ((cur_size - asize) >= 2 * DSIZE) {
    PUT(HDRP(bp), PACK(asize, FLAG_ALLOCATED));
    PUT(FTRP(bp), PACK(asize, FLAG_ALLOCATED));

    // 분할 : 여유 블록 초기화
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(cur_size - asize, 0));
    PUT(FTRP(bp), PACK(cur_size - asize, 0));
  } else {
    PUT(HDRP(bp), PACK(cur_size, FLAG_ALLOCATED));
    PUT(FTRP(bp), PACK(cur_size, FLAG_ALLOCATED));
  }
}