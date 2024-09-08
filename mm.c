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

typedef enum { FREE = 0, ALLOCATED = 1 } BlockStatus;

/*explicit code*/
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4                    /* Word and header/footer size (bytes) */
#define DSIZE 8                    /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12)        /* Extend heap by this amount (bytes) */
#define MIN_BLOCK_SIZE (DSIZE * 2) // Minimum block size or length 8(header + footer) + 8(payload has prev, next)

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
static char *heap_listp;
static char *free_listp;
static void *coalesce_with_LIFO(void *bp);
void remove_in_freelist(void *bp);
void put_front_of_freelist(void *bp, size_t);
static void *extend_heap(size_t words);
// void *mm_malloc(size_t size);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void set_block(void *bp, size_t size, BlockStatus alloced);

/* for explicit*/
#define PREV_FREEP(bp) (*(void **)(bp))
#define NEXT_FREEP(bp) (*(void **)(bp + WSIZE))

/*  mm_init - initialize the malloc package  */
int mm_init(void) { /* Create the initial empty heap */

    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) // 할당을 못해주면, null 대신 (voi *) -1
        return -1;
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE * 2, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), NULL);               /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), NULL);               /* PREV */
    PUT(heap_listp + (4 * WSIZE), PACK(DSIZE * 2, 1)); /* NEXT */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header */
    heap_listp += (2 * WSIZE);
    free_listp = heap_listp;

    if (extend_heap(4) == NULL)
        return -1;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
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
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) // 헤더 푸터 쓰고나면 데이터 들어갈 곳이 0칸이므로.... 4칸으로 늘려줌
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 헤더 푸터 넣어주어야하니까 데이터 넣을 수 있는거 + 2칸 더 넣어주어야 함
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize); // find로 우리가 찾았음... 그 다음에, 찾은 녀석이 size보다 작을거 아님? 그러면
        return bp;        // 찾은 free영역에서 내가 원하는 크기만큼 place시켜줌
    }
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 // find 했을 때, 적당한 애를 못찾았을 때, 힙을 확장해줌
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 8바이트씩
        return NULL;
    place(bp, asize);
    return bp;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 더블 워드 정렬 유지
    if ((long)(bp = mem_sbrk(size)) == -1)                           // 힙 확장
        return NULL;

    // put_front_of_freelist(bp, size); // 오답
    set_block(bp, size, FREE);            // 정답
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // New epilogue header
    return coalesce_with_LIFO(bp);
}

void mm_free(void *ptr) {
    size_t size = GET_SIZE(HDRP(ptr));
    set_block(ptr, size, FREE);
    coalesce_with_LIFO(ptr);
}

static void *coalesce_with_LIFO(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        /* Case 1 : same as */
        put_front_of_freelist(bp, size); // TODO: 뒤로 한꺼번에 빼기
        return bp;
    } else if (prev_alloc && !next_alloc) {
        /**
         * Case 2 : new block
         * - header : bp
         * - footer : bp (w. new bp size)
         * */

        char *first_free_bp = bp;
        char *second_free_bp = NEXT_BLKP(bp);
        remove_in_freelist(second_free_bp);

        // free 블록 병합 (resize)
        size += GET_SIZE(HDRP(second_free_bp));
        PUT(HDRP(first_free_bp), PACK(size, FREE));
        PUT(FTRP(first_free_bp), PACK(size, FREE));

        // new free blocks 앞에 연결
        put_front_of_freelist(first_free_bp, size);
        return first_free_bp;
    } else if (!prev_alloc && next_alloc) {
        /**
         * Case 3 : new block
         * - header : HDRP(PREV_BLKP(bp)
         * - footer : FTRP(bp)
         * */

        char *first_free_bp = PREV_BLKP(bp);
        remove_in_freelist(first_free_bp);

        // free 블록 병합 (resize)
        char *second_free_bp = bp;
        size += GET_SIZE(HDRP(first_free_bp));
        PUT(FTRP(second_free_bp), PACK(size, FREE)); // TODO: 아래로 내려도 될지?
        PUT(HDRP(first_free_bp), PACK(size, FREE));

        put_front_of_freelist(first_free_bp, size);
        return first_free_bp;
    } else {
        /**
         * Case 4 : new block
         * - header : HDRP(PREV_BLKP(bp))
         * - footer : FTRP(NEXT_BLKP(bp))
         * */

        char *first_free_bp = PREV_BLKP(bp);
        char *third_free_bp = NEXT_BLKP(bp);
        remove_in_freelist(first_free_bp);
        remove_in_freelist(third_free_bp);

        // free 블록 병합 (resize)
        size += GET_SIZE(HDRP(first_free_bp)) + GET_SIZE(FTRP(third_free_bp));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, FREE));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, FREE));

        put_front_of_freelist(first_free_bp, size);
        return first_free_bp;
    }
}

void remove_in_freelist(void *bp) {
    // 현재 block 기준으로 prev, next block 찾기
    char *prev_bp = PREV_FREEP(bp);
    char *next_bp = NEXT_FREEP(bp);

    if (prev_bp != NULL) {
        // 이전 블록이 있는 경우, 이전 블록의 next를 현재 블록의 next로 연결
        NEXT_FREEP(prev_bp) = next_bp;
    } else {
        // 이전 블록이 없는 경우 (즉, 첫 번째 블록인 경우), 시작 포인터를 다음 블록으로 갱신
        free_listp = next_bp;
    }

    if (next_bp != NULL) {
        // 다음 블록이 있는 경우, 다음 블록의 prev를 현재 블록의 prev로 연결
        PREV_FREEP(next_bp) = prev_bp;
    }
}

void put_front_of_freelist(void *bp, size_t size) {
    // NEXT_FREEP(bp) = free_listp;
    // PREV_FREEP(bp) = NULL;
    // PREV_FREEP(free_listp) = bp;
    // free_listp = bp; // bp가 첫번째 블럭이므로

    // 신규 블록
    set_block(bp, size, FREE);
    NEXT_FREEP(bp) = free_listp; // next 연결
    PREV_FREEP(bp) = NULL;       // prev 연결
    PREV_FREEP(free_listp) = bp; // 기존 블록의 prev를 새 블록으로 연결

    free_listp = bp; // 갱신
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */

// 내꺼
static void *find_fit(size_t asize) //
{
    void *bp = free_listp;
    while (bp != NULL) {
        if (asize <= GET_SIZE(HDRP(bp))) {
            return bp;
        }
        bp = NEXT_FREEP(bp);
    }
    return NULL;
}

// 내꺼
static void place(void *bp, size_t asize) {

    size_t cur_size = GET_SIZE(HDRP(bp));
    size_t remain_size = cur_size - asize;

    // prev, next block 연결
    remove_in_freelist(bp);

    if (remain_size >= MIN_BLOCK_SIZE) {
        // 분할
        set_block(bp, asize, ALLOCATED);
        char *free_bp = NEXT_BLKP(bp);

        // 분할된 new free blocks 앞에 연결
        put_front_of_freelist(free_bp, remain_size);

    } else {
        set_block(bp, cur_size, ALLOCATED); // w. padding
    }
}

void *mm_realloc(void *ptr, size_t size) {
    // realloc 을 할 수 없는 경우 밑에 if문 2가지 케이스
    if (size <= 0) {
        // 사이즈를 0으로 변경한 것은 free 한것과 동일함. 따라서 free 시켜준다.
        mm_free(ptr);
        return 0;
    }
    if (ptr == NULL) {
        // 애초에 크기를 조정할 블록이 존재하지 않았다. 그냥 할당한다 ( malloc )
        return mm_malloc(size);
    }
    // malloc 함수의 리턴값이 newp가 가리키는 주소임.

    void *newp = mm_malloc(size);
    // newp가 가리키는 주소가 NULL(할당되었다고 생각했지만 실패한 경우)
    if (newp == NULL) {
        return 0;
    }
    // 진짜 realloc 하는 코드임.
    size_t oldsize = GET_SIZE(HDRP(ptr));
    // ex int a(oldsize) = 10(GET_SIZE(HDRP(ptr));)
    // 그러므로 일단 여기까진 a = 10
    // 재할당이라는 것은 get_size 한 10값을 a(기존데이터주소)가 아닌 b(다른데이터주소)
    // 에 넣는다는 것이다.
    /*
    새로 할당하고자 하는 크기가 oldsize 보다 작으면
    그런데 oldsize가 가진 데이터의 크기가 size의 데이터 크기보다 크기때문에
    커서 전부 다 못들어간다. 그러면은 일단 size 만큼의 데이터만 size에 재할당하고
    나머지 부분(데이터)는 버린다. (가비지데이터)
    */
    if (size < oldsize) {
        oldsize = size; // oldsize의 데이터크기를 size 크기만큼 줄이겠다는 뜻.
    }
    // oldsize 데이터를  ptr(기존 주소) 에서 newp(새로 할당될 주소) 로 옮겨준다.
    memcpy(newp, ptr, oldsize);
    mm_free(ptr); // 원래 기존 주소에 있던 데이터를 free 시킨다.
    // 새로 할당된 데이터의 주소를 리턴한다.
    return newp;
}

static void set_block(void *bp, size_t size, BlockStatus alloced) {
    PUT(HDRP(bp), PACK(size, alloced));
    PUT(FTRP(bp), PACK(size, alloced));
}