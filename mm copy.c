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

#define WSIZE 4
#define DSIZE 8
#define LISTLIMIT 12
#define CHUNKSIZE (1<<6)

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
#define GET_ROOT(class) (*(void **)((char *)(heap_listp) + (WSIZE * class)))

#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
/* 
 * mm_init - initialize the malloc package.
 */
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *extend_heap(size_t words);
static void *coalesce(void *bp);


static char* heap_listp = NULL;
/* next fit variable */
// static char* prev_bp = NULL;
int mm_init(void)
{   
    if((heap_listp = mem_sbrk((4 + LISTLIMIT)*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0);
    PUT(heap_listp + 1*WSIZE, PACK((LISTLIMIT + 2)*WSIZE, 1)); // prologue header
    for(int i = 0; i < LISTLIMIT; i++){
        PUT(heap_listp + (2 + i)*WSIZE, NULL);
    }
    PUT(heap_listp + (2 + LISTLIMIT)*WSIZE, PACK((LISTLIMIT + 2)*WSIZE, 1)); // prologue footer
    PUT(heap_listp + (3 + LISTLIMIT)*WSIZE, PACK(0, 1)); // epilogue

    heap_listp += (2 * WSIZE);
    
    if (extend_heap(4) == NULL)
        return -1;
    if(extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

static void list_add(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    int class = get_class(size);

    SUCC_FREEP(bp) = GET_ROOT(class);
    if(GET_ROOT(class) != NULL){
        PRED_FREEP(GET_ROOT(class)) = bp;
    }
    GET_ROOT(class) = bp;
    }


static void list_remove(void *bp){
    size_t size = GET_SIZE(HDRP(bp));
    int class = get_class(size);
    if(GET_ROOT(class) == bp){
        GET_ROOT(class) = SUCC_FREEP(bp);
    }else{
        if(SUCC_FREEP(bp) != NULL){
            PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp);
            SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp);
        }else{
            SUCC_FREEP(PRED_FREEP(bp)) = NULL;
        }
    }
}

 static void place(void *bp, size_t asize)
    {
        list_remove(bp); // free_list에서 해당 블록 제거

        size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기

        if ((csize - asize) >= (2 * DSIZE)) // 차이가 최소 블록 크기 16보다 같거나 크면 분할
        {
            PUT(HDRP(bp), PACK(asize, 1)); // 현재 블록에는 필요한 만큼만 할당
            PUT(FTRP(bp), PACK(asize, 1));

            PUT(HDRP(NEXT_BLKP(bp)), PACK((csize - asize), 0)); // 남은 크기를 다음 블록에 할당(가용 블록)
            PUT(FTRP(NEXT_BLKP(bp)), PACK((csize - asize), 0));
            list_add(NEXT_BLKP(bp)); // 남은 블록을 free_list에 추가
        }
        else
        {
            PUT(HDRP(bp), PACK(csize, 1)); // 해당 블록 전부 사용
            PUT(FTRP(bp), PACK(csize, 1));
        }
    }

int get_class(size_t size){
    if(size < 16) return -1;

    size_t size_dp[LISTLIMIT];
    size_dp[0] = 16;

    for(int i = 0; i < LISTLIMIT; i++){
        if(i != 0)
            size_dp[i] = size_dp[i-1] << 1;
        if(size_dp[i] >= size){
            return i;
        }
    }
    return LISTLIMIT - 1;
}

static void *find_fit(size_t asize)
{   
    int class = get_class(asize);
    void *result_bp = NULL;
    void* bp;
    while(class < LISTLIMIT){
        bp = GET_ROOT(class);
        while(bp != NULL){
            if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){
                if(result_bp != NULL && GET_SIZE(HDRP(result_bp)) > GET_SIZE(HDRP(bp))){
                    result_bp = bp;
                }
                if(result_bp == NULL){
                    result_bp = bp;
                }
            }
            bp = SUCC_FREEP(bp);
        }
        class += 1;
    }
    return result_bp;
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


void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록 할당 상태
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록 할당 상태
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록 사이즈

    if (prev_alloc && next_alloc) // 모두 할당된 경우
    {
        list_add(bp); // free_list에 추가
        return bp;          // 블록의 포인터 반환
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 빈 경우
    {
        list_remove(NEXT_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0)); // 현재 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0)); // 다음 블록 푸터 재설정 (위에서 헤더를 재설정했으므로, FTRP(bp)는 합쳐질 다음 블록의 푸터가 됨)
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 빈 경우
    {
        list_remove(PREV_BLKP(bp)); // 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    else // 이전 블록과 다음 블록 모두 빈 경우
    {
        list_remove(PREV_BLKP(bp)); // 이전 가용 블록을 free_list에서 제거
        list_remove(NEXT_BLKP(bp)); // 다음 가용 블록을 free_list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록 헤더 재설정
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 블록 푸터 재설정
        bp = PREV_BLKP(bp);                      // 이전 블록의 시작점으로 포인터 변경
    }
    list_add(bp); // 현재 병합한 가용 블록을 free_list에 추가
    return bp;          // 병합한 가용 블록의 포인터 반환
}

void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    void *bp;

    if(size == 0)
        return NULL;
    
    int asize = ALIGN(size + SIZE_T_SIZE);
    
    if((bp = find_fit(asize)) != NULL){
        place(bp, asize);
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

int can_coalesce(void* ptr){

    if(GET_ALLOC(FTRP(PREV_BLKP(ptr))) == 0 || GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0){
        return 1;
    }
    return -1;
}

void mm_resize(void){
    for(int i = 0; i < LISTLIMIT; i++){
        void* bp = GET_ROOT(i);
        while(bp != NULL){
            if(can_coalesce(bp) == 1){
                bp = coalesce(bp);
            }else{
                bp = SUCC_FREEP(bp);
            }
        }
    }
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    size_t asize;
    // 요청 사이즈가 0이면 할당 블록 반환
    if(size == 0){
        mm_free(oldptr);
        return NULL;
    }
    
    // 요청 사이즈의 블록 정렬
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);
    copySize = GET_SIZE(HDRP(oldptr));

    if (asize < copySize){
        return oldptr;
    }

    // 할당된 블록의 사이즈가 요청 사이즈보다 
    void* prev_bp = PREV_BLKP(oldptr);
    size_t prev_size = GET_SIZE(HDRP(prev_bp));
    void* next_bp = NEXT_BLKP(oldptr);
    size_t next_size = GET_SIZE(HDRP(next_bp));

    if (!GET_ALLOC(FTRP(PREV_BLKP(oldptr))) && prev_size > asize){
        memmove(prev_bp, oldptr, asize);
        list_remove(prev_bp);
        PUT(HDRP(prev_bp), PACK(prev_size, 1));
        PUT(FTRP(prev_bp), PACK(prev_size, 1));
        mm_free(oldptr);
        return prev_bp;
    }

    if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && next_size > asize){
        memmove(next_bp, oldptr, asize);
        list_remove(next_bp);
        PUT(HDRP(next_bp), PACK(next_size, 1));
        PUT(FTRP(next_bp), PACK(next_size, 1));
        mm_free(oldptr);
        return next_bp;
    }

    if(!GET_ALLOC(FTRP(PREV_BLKP(oldptr))) && prev_size + copySize > asize){
        memmove(prev_bp, oldptr, asize);
        list_remove(prev_bp); // 가용 블록을 free_list에서 제거
        PUT(HDRP(prev_bp), PACK(copySize+prev_size, 1));
        PUT(FTRP(prev_bp), PACK(copySize+prev_size, 1));
        return prev_bp;
    }

    if(!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && next_size + copySize > asize){
        list_remove(next_bp); // 가용 블록을 free_list에서 제거
        PUT(HDRP(oldptr), PACK(copySize+next_size, 1));
        PUT(FTRP(oldptr), PACK(copySize+next_size, 1));
        return oldptr;
    }

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;

    memmove(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;

}