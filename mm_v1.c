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
// #define ALIGNMENT 4
// #define DALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (DSIZE-1)) & ~0x7)


// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4
#define DSIZE 8
#define BSIZE 16
#define CHUNKSIZE (1<<12)

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc) ((size) | (alloc))

#define GET(p) (*(unsigned int *)(p))

#define PUT(p, val) (*(unsigned int *)(p) = (val))
// #define PUT_ADDR(p, val) (*(unsigned int **)(p) = (val))

#define GET_SIZE(p) ((GET(p) & ~0x7))
#define GET_ALLOC(p) ((GET(p) & 0x1))

#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define PRED_FREEP(bp) (GET(bp))
// #define SUCC_FREEP(bp) (*(void ******************)(bp))
#define SUCC_FREEP(bp) (GET((bp)+WSIZE))
/* 
 * mm_init - initialize the malloc package.
 */
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static char* heap_listp = NULL;
static char* free_listp = NULL;

/* next fit variable */
// static char* prev_bp = NULL;
int mm_init(void)
{   
    if((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + (1*WSIZE), PACK(BSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), NULL); // predeccessor
    PUT(heap_listp + (3*WSIZE), NULL); // successor
    PUT(heap_listp + (4*WSIZE), PACK(BSIZE, 1)); // prologue footer
    PUT(heap_listp + (5*WSIZE), PACK(0, 1)); // epilogue
    free_listp = heap_listp + 2*WSIZE;
    extend_heap(4);
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void list_add(void *bp){
    // PUT(SUCC_FREEP(bp), (unsigned int *)free_listp);
    // PUT(PRED_FREEP(bp), NULL);
    // PUT(PRED_FREEP(free_listp), (unsigned int *)bp);
    // free_listp = bp;
    void *curr_bp = free_listp;
    if (curr_bp == NULL)
    {
        free_listp = bp;
        SUCC_FREEP(bp) = NULL;
        return;
    }

    for(curr_bp = free_listp; GET_ALLOC(HDRP(curr_bp)) == 0; curr_bp = (void *)SUCC_FREEP(curr_bp)){
        if(bp < SUCC_FREEP(curr_bp)){
            PRED_FREEP(bp) = curr_bp;
            SUCC_FREEP(curr_bp) = bp;
            SUCC_FREEP(bp) = SUCC_FREEP(curr_bp);
            
            if(SUCC_FREEP(curr_bp) == NULL) {
                PRED_FREEP(SUCC_FREEP(curr_bp)) = bp;
                }
            return;
            }
        }
    // SUCC_FREEP(bp) = free_listp;
    // PRED_FREEP(bp) = NULL;
    // PRED_FREEP(free_listp) = bp;
    }


static void list_remove(void *bp){
    // if (bp == free_listp){
    //     PUT((char *)PRED_FREEP(SUCC_FREEP(bp)), NULL);
    //     free_listp = SUCC_FREEP(bp);
    // }
    // // free list 안에서 없앨 때
    // else{
    //     PUT((char *)PRED_FREEP(SUCC_FREEP(bp)), (unsigned int *)PRED_FREEP(bp));
    //     PUT((char *)SUCC_FREEP(PRED_FREEP(bp)), (unsigned int *)SUCC_FREEP(bp));
    // }
    if (bp == free_listp) // 분리하려는 블록이 free_list 맨 앞에 있는 블록이면 (이전 블록이 없음)
    {
        free_listp = SUCC_FREEP(free_listp); // 다음 블록을 루트로 변경
        return;
    }
    // 이전 블록의 SUCC을 다음 가용 블록으로 연결
    SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
    // 다음 블록의 PRED를 이전 블록으로 변경
    if (SUCC_FREEP(bp) != NULL) // 다음 가용 블록이 있을 경우만
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
}

static void place(void *bp, size_t asize)
{   
    size_t free_size = GET_SIZE(HDRP(bp));
    if(free_size >= asize + 2*DSIZE){
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(free_size - asize, 0));
        PUT(FTRP(bp), PACK(free_size - asize, 0));
        
        SUCC_FREEP(bp) = SUCC_FREEP(PREV_BLKP(bp));

        if (PREV_BLKP(bp) == free_listp) 
        {
            free_listp = bp;
        }
        else
        {
            PRED_FREEP(bp) = PRED_FREEP(PREV_BLKP(bp));
            SUCC_FREEP(PRED_FREEP(PREV_BLKP(bp))) = bp;
        }

        if (SUCC_FREEP(bp) != NULL) // 다음 가용 블록이 있을 경우만
            PRED_FREEP(SUCC_FREEP(bp)) = bp;
    
    }else{
        list_remove(bp);
        PUT(HDRP(bp), PACK(free_size, 1));
        PUT(FTRP(bp), PACK(free_size, 1));
    }
}

static void *find_fit(size_t asize)
{
    /* best fit */
    // void *result_bp = NULL;
    // void *bp = heap_listp;
    // while(GET_SIZE(HDRP(bp)) > 0){
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         if(result_bp != NULL && GET_SIZE(bp) < GET_SIZE(result_bp)){
    //             result_bp = bp;
    //         }
    //         if(result_bp == NULL){
    //             result_bp = bp;
    //         }
    //     }
    //     bp = NEXT_BLKP(bp);
    // }

    /* next fit */
    // void *bp = prev_bp ? prev_bp : heap_listp;
    // while(GET_SIZE(HDRP(bp)) > 0){
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         prev_bp = bp;
    //         return bp;
    //     }
    //     bp = NEXT_BLKP(bp);
    // }
    // bp = heap_listp;
    // while(GET_SIZE(HDRP(bp)) > 0){
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
    //         prev_bp = bp;
    //         return bp;
    //     }
    //     if (bp == prev_bp){
    //         return NULL;
    //     }
    //     bp = NEXT_BLKP(bp);
    // }
    
    /* first fit */
    for (void* bp = free_listp; GET_ALLOC(HDRP(bp)) == 0; bp = (void *)SUCC_FREEP(bp)){
        if(asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// void *mm_malloc(size_t size)
// {
//     int newsize = ALIGN(size + SIZE_T_SIZE);
//     void *p = mem_sbrk(newsize);
//     if (p == (void *)-1)
// 	return NULL;
//     else {
//         *(size_t *)p = size;
//         return (void *)((char *)p + SIZE_T_SIZE);
//     }
// }

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if(prev_alloc && next_alloc){
        list_add(bp);
        return bp;
    }
    else if(prev_alloc && !next_alloc){
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(bp), PACK(size, 0));
        list_add(bp);
    }
    else if(!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
    }
    else if (!prev_alloc && !next_alloc){
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 앞 블록 헤더 사이즈 업데이트
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 뒤 블록 풋터 사이즈 업데이트
        bp = PREV_BLKP(bp);
    }
    // prev_bp = bp;
    return bp;
}

// static void *explicit_coalesce(void *bp)
// {
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     size_t size = GET_SIZE(HDRP(bp));

//     if(prev_alloc && !next_alloc){
//         list_remove(NEXT_BLKP(bp));
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         PUT(HDRP(bp), PACK(size, 0));
//     }
//     else if(!prev_alloc && next_alloc){
//         list_remove(PREV_BLKP(bp));
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//         PUT(HDRP(bp), PACK(size, 0));
//     }
//     else if (!prev_alloc && !next_alloc){
//         list_remove(PREV_BLKP(bp));
//         list_remove(NEXT_BLKP(bp));
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
//             GET_SIZE(FTRP(NEXT_BLKP(bp)));
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));    // 앞 블록 헤더 사이즈 업데이트
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));    // 뒤 블록 풋터 사이즈 업데이트
//         bp = PREV_BLKP(bp);
//     }
//     // prev_bp = bp;
//     list_add(bp);
//     return bp;
// }

// static void *coalesce(void *bp)
// {
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
//     size_t size = GET_SIZE(HDRP(bp));

//     if(prev_alloc && !next_alloc){
//         return bp;
//     }
//     else if(prev_alloc && !next_alloc){
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         PUT(HDRP(bp), PACK(size, 0));
//     }
//     else if(!prev_alloc && next_alloc){
//         size += GET_SIZE(HDRP(PREV_BLKP(bp)));
//         PUT(FTRP(bp), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//         PUT(HDRP(bp), PACK(size, 0));
//     }
//     else {
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
//             GET_SIZE(FTRP(NEXT_BLKP(bp)));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
//         bp = PREV_BLKP(bp);
//         PUT(HDRP(bp), PACK(size, 0));
//     }
//     // prev_bp = bp;
//     return bp;
// }

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if(size == 0)
        return NULL;
    
    if(size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE*((size + (DSIZE) + (DSIZE-1))/ DSIZE);
    
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }
    // }else{
    //     for(bp = heap_listp; GET_SIZE(bp)>0; bp = NEXT_BLKP(bp)){
    //         if(!GET_ALLOC(bp)){
    //             coalesce(bp);
    //         }
    //     }
    // }

    // if((bp = find_fit(asize)) != NULL){
    //     place(bp, asize);
    //     return bp;
    // }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = GET_SIZE(HDRP(oldptr));
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}














