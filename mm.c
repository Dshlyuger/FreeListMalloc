/*
* mm.c
Daniel Shlyuger
*/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to prologue block */
static char *headOfFreeList = 0; /* Pointer to first block */
static char *headOfFreeList2 = 0; /* Pointer to second block */
static char *headOfFreeList3 = 0; /* Pointer to third block */
static char *headOfFreeList4 = 0; /* Pointer to forth block */
static char *headOfFreeList5 = 0; /* Pointer to fifth block */
static char *headOfFreeList6 = 0; /* Pointer to sixth block */
static char *headOfFreeList7 = 0; /* Pointer to seventh block */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

#define MAX(x, y) ((x) > (y)? (x) : (y))
/* Basic constants and macros */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE        4       // Word and header/footer size (bytes)
#define DSIZE        8       // Doubleword size (bytes)
#define MINSIZE     16       // Minsize of a block
#define CHUNKSIZE   170      // Extend heap by this amount (bytes)

#define CHECKFROMFIT 12      /* Number of blocks to check for better fit from
the first fit that is found */
#define NUMLISTS 7           // Number of segreated lists

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))
#define PUT(p, val)  (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// Return pointer to previous block in the freelist
static inline void* prev(void* bp) {
    unsigned int offsetOfPrev = GET(bp);
    void * prevBlock = (void *)((offsetOfPrev) + heap_listp);
    return prevBlock;
}

// Return pointer to next word of input pointer
static inline void* getNextWord(void* bp){
    return (void*)(((char *)(bp)) + WSIZE);
}

// Return pointer to next block in the free list
static inline void* next(void* bp) {
    void* startOfNext = getNextWord(bp);
    unsigned int offsetOfNext = GET(startOfNext);
    void * nextBlock = (void *)((offsetOfNext) + heap_listp);
    return nextBlock;
}

/* Given block ptr bp, compute address of next and previous blocks */
static inline void* NEXT_BLKP(void* bp) {
    return ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) ;
}
static inline void* PREV_BLKP(void* bp) {
    return ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)));
}

// Given a particualr number return pointer to the head of that ith list
static inline char ** freeListStart(int numList) {
    switch(numList)
    {
        case 1:
        return &headOfFreeList;
        break;
        case 2 :
        return &headOfFreeList2;
        case 3 :
        return &headOfFreeList3;
        case 4 :
        return &headOfFreeList4;
        case 5 :
        return &headOfFreeList5;
        break;
        case 6 :
        return &headOfFreeList6;
        break;
        case 7 :
        return &headOfFreeList7;
        break;
        
    }
    return 0;
}


// Given a block size return the ith list that holds blocks of that size
static inline unsigned int approrpriateFreeList(unsigned int asize) {
    if(asize >= 16 && asize<=31){
        return 1;
    }
    
    if(asize >= 32 && asize<=63){
        return 2;
    }
    
    if(asize >= 64 && asize <=127){
        return 3;
    }
    
    if(asize >= 128 && asize <=255){
        return 4;
    }
    
    if(asize >= 256 && asize <=511){
        return 5;
    }
    
    if(asize >= 512 && asize <=1023){
        return 6;
    }
    return 7;
    
    
}

// Calculate offset from the prologue of the input block
static inline int offsetFromPrologue(void* bp) {
    return ((char*)bp) - heap_listp;
}

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void checkblock(void *bp);

/* mm_init - Initialize the memory manager as well as  pointers to the heads
of the included free lists */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1)
    return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2 * WSIZE);
    
    /* By defalut all freelists point to the prologue as their head to indicate
    that they are empty */
    
    headOfFreeList = heap_listp;
    headOfFreeList2 = heap_listp;
    headOfFreeList3 = heap_listp;
    headOfFreeList4 = heap_listp;
    headOfFreeList5 = heap_listp;
    headOfFreeList6 = heap_listp;
    headOfFreeList7 = heap_listp;
       
    return 0;
}

/* Adds the given blockpointer to the free list that contains pointers of it's
size  */
static inline void addToFront(void* bp, char** freeListPointer){
    
    char* castedBp = (char*)(bp);
    /* The block is now the head of the freelist so it now points to
    the prologue */
    PUT(castedBp,offsetFromPrologue(heap_listp));
    
    // Case 1 the free list is empty
    if(*freeListPointer == heap_listp) {
        // In this case we make the new block point to the epilogue
        char * nextWord = getNextWord(castedBp);
        PUT(nextWord,offsetFromPrologue(heap_listp));
    }
    // Otherwise it now points to the old head of the free list.
    else{
        char * nextWord = getNextWord(castedBp);
        /* This is the location of the current head of the free list
        We then make our new head point to the old head; */
        
        PUT(nextWord,offsetFromPrologue(*freeListPointer));
        
        // Make old head previous point to the new of the list;
        
        // This line is causing problems, might want to find out why later.
        PUT(*freeListPointer,offsetFromPrologue(castedBp));
    }
    
    // The new head is now the head of the list.
    *freeListPointer = castedBp;
}


// Deletes the input block from it's free list
static inline void deleteFromFreeList(void* bp){
    
    char* castedBp = (char*)(bp);
    char * prevBlockInFreeList = (char*)((prev(castedBp)));
    char * nextBlockInFreeList = (char*)((next(castedBp)));
    
    /* In this case we are deleting a block in the middle of two free blocks*/
    if(prevBlockInFreeList != heap_listp && nextBlockInFreeList != heap_listp){
        // preddessor block now points to the deleted blocks successor;
        PUT(getNextWord(prevBlockInFreeList),
        offsetFromPrologue(nextBlockInFreeList));
        // successor block now points back to deleted blocks preddessor;
        PUT(nextBlockInFreeList,offsetFromPrologue(prevBlockInFreeList));
        return;
    }
    // In this case blocks free list is other then the input block, empty;
    else if(prevBlockInFreeList == heap_listp
    && nextBlockInFreeList == heap_listp) {
        int appList = approrpriateFreeList(GET_SIZE(HDRP(bp)));
        // Indicates this freelist is now empty;
        *(freeListStart(appList)) = heap_listp;
    }
    // In this case input block points to the epilogue
    else if(nextBlockInFreeList == heap_listp){
        // in this case previous block now points to end
        PUT(getNextWord(prevBlockInFreeList),offsetFromPrologue(heap_listp));
        return;
    }
    
    else {
        /* In this case we are deleting the front of the freelist so
        our successor block now points to the prologue and is the head
        of the free list*/
        PUT(nextBlockInFreeList,offsetFromPrologue(heap_listp));
        int appList = approrpriateFreeList(GET_SIZE(HDRP(bp)));
        *(freeListStart(appList)) = nextBlockInFreeList;
    }
}

/*
* calloc - Allocate the block and set it to zero.
*/
void *calloc (size_t nmemb, size_t size)
{
    size_t bytes = nmemb * size;
    void *newptr;
    
    newptr = malloc(bytes);
    memset(newptr, 0, bytes);
    
    return newptr;
}


/*
* mm_malloc - Allocate a block with at least size bytes of payload
*/
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
    if (heap_listp == 0) {
        mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
    return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    }
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        deleteFromFreeList(bp);
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

// Frees the input block
void mm_free(void *bp)
{
    if (bp == 0)
    return;
    
    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0) {
        mm_init();
    }
    // Sets header and footer to indicate that the blocks are unallocated
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // coalesces newly free block with adjacent blocks
    void* coalasced = coalesce(bp);
    unsigned int sizeCoalsced = GET_SIZE(HDRP(coalasced));
    // Adds new "mega block" to the appropriate free list
    addToFront(coalasced,(freeListStart(approrpriateFreeList(sizeCoalsced))));
}

// mm_realloc - Naive implementation of realloc

void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
    void *newptr;
    
    // If size == 0 then this is just free, and we return NULL. //
    if (size == 0) {
        mm_free(ptr);
        return 0;
    }
    
    // If oldptr is NULL, then this is just malloc. //
    if (ptr == NULL) {
        return mm_malloc(size);
    }
    
    newptr = mm_malloc(size);
    
    // If realloc() fails the original block is left untouched //
    if (!newptr) {
        return 0;
    }
    
    // Copy the old data. //
    oldsize = GET_SIZE(HDRP(ptr));
    if (size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);
    
    // Free the old block. //
    mm_free(ptr);
    return newptr;
}

// coalesce - Boundary tag coalescing. Return ptr to coalesced block

static inline void *coalesce(void *bp)
{
    void* prevBlock = PREV_BLKP(bp);
    void* nextBlock = NEXT_BLKP(bp);
    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    // Case 1 adjacent blocks are already allocated //
    if (prev_alloc && next_alloc) {
        return bp;
    }
    
    // Case 2 only next block is unallocated //
    else if (prev_alloc && !next_alloc) {
        deleteFromFreeList(nextBlock);
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
    }
    // Case 3 only previous block is unallocated //
    else if (!prev_alloc && next_alloc) {
        deleteFromFreeList(prevBlock);
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    // Both blocks are unallocated//
    else {
        deleteFromFreeList(prevBlock);
        deleteFromFreeList(nextBlock);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
    }
    
    return bp;
}

/*
* extend_heap - Extend heap with free block and return its block pointer
*/
static inline void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    /* Insert Prev Free Block offset */
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    void* coalasced = coalesce(bp);
    return coalasced;
}
/*
* place - Place block of asize bytes at start of free block bp
*         and split if remainder would be at least minimum block size
*/
static inline void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    /* Split block if neccessary and add newly created block to approrpriate
    free list */
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        char* newBlock = NEXT_BLKP(bp);
        PUT(HDRP(newBlock), PACK(csize - asize, 0));
        PUT(FTRP(newBlock), PACK(csize - asize, 0));
        addToFront(newBlock,(freeListStart(approrpriateFreeList(csize-asize))));
        
    }
    // No need to split block
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/* Given a block that fits the current size looks CHECKFROMFIT
blocks ahead to see if any block is a better fit i.e  of a size that is
closer to the requeste block size*/
static inline void* bestFitEstimate(void* bp, unsigned int asize){
    unsigned int greatestDif = GET_SIZE(HDRP(bp)) - asize;
    char* bestFit = bp;
    int numToCheck = CHECKFROMFIT;
    for (char * curBlock = bp; numToCheck && curBlock && ((char *)(curBlock))
    !=heap_listp; curBlock = next(curBlock)) {
        if ((asize <= GET_SIZE(HDRP(bp)))) {
            
            if((GET_SIZE(HDRP(curBlock)) - asize) < greatestDif){
                greatestDif = GET_SIZE(HDRP(bp)) - asize;
                bestFit = curBlock;
            }
        }
        numToCheck--;
    }
    
    return bestFit;
}
/*
* find_fit - Find a fit for a block with asize bytes
*/
static inline void *find_fit(size_t asize) {
    void *bp;
    // We start from the smallest free list that contains blocks of that size
    for(int start = approrpriateFreeList(asize); start<NUMLISTS+1; start++){
        // Searching inside a particular free list
        for (bp = *(freeListStart(start)); bp && bp!=heap_listp; bp = next(bp)){
            if ((asize <= GET_SIZE(HDRP(bp)))) {
                return bestFitEstimate(bp,asize);
            }
        }
    }
    // Return null if we have no free blocks that are a fit
    return NULL;
}

// Return whether the pointer is in the heap.
static int in_heap(const void *p) {
    return p <= mem_heap_hi() && p >= mem_heap_lo();
}

// Returns whether a pointer is aligned
static int aligned(const void *p) {
    return (size_t)ALIGN(p) == (size_t)p;
}

/* Makes sure a particular block abides by the invarients set by the
implementation */
static void checkblock(void *bp)
{
    if ((size_t)bp % 8){
        printf("Error: %p is not doubleword alignedn", bp);
        exit(0);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))){
        printf("Error: header does not match footer");
        exit(0);
    }
    
    if(!in_heap(bp)){
        printf("block is not in the heap");
        exit(0);
    }
    
    if(GET_ALLOC(HDRP(bp)) != GET_ALLOC(FTRP(bp))){
        printf("header and footer alloc bits don't match");
        exit(0);
    }
    
    if(!aligned(bp)){
        printf("Not properly aligned");
        exit(0);
    }
    
    if(GET_SIZE(HDRP(bp)) < MINSIZE){
        printf("Block is smaller then the minimum size");
        exit(0);
    }
    
}

/* checkheap - Makes sure the heap abides by the invarients set by the
implementation. */
void mm_checkheap(int lineNumber)
{
    
    char *bp = heap_listp;
    int totalFree = 0;
    int totalFreeInLists = 0;
    
    // Makes sure prologue header is correct
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))){
        printf("Bad prologue headern");
        checkblock(heap_listp);
        printf("Checked in line Number %d",lineNumber);
        exit(0);
    }
    
    /* Counts free blocks in heap, makes sure each block is coalesced and 
       correct */
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if(!GET_ALLOC(FTRP(bp))){
            totalFree++;
        }
        
        if(GET_SIZE(HDRP(NEXT_BLKP(bp))) > 0 && bp !=heap_listp){
            if(!GET_ALLOC(FTRP(bp)) && !GET_ALLOC(FTRP(NEXT_BLKP(bp)))){
                printf("There are uncoalseced blocksn");
                printf("Checked in line Number %d",lineNumber);
                exit(0);
            }
        }
        
        checkblock(bp);
    }
    
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) {
        printf("Bad epilogue headern");
        printf("Checked in line Number %d",lineNumber);
    }
    /* Counts freeblocks, checks that pointers are consistent and each
    freeblock is a valid block. Also checks that each block is in the right
    bucket. In addition impliitly checks for cycles, if there were cycles
    code would never finish executing. Lastly checks that there are no
    allocated blocks in the free list */
    
    for(int start = 1; start<NUMLISTS; start++){
        for (bp = *(freeListStart(start)); bp &&
        ((char *)(bp))!=heap_listp; bp = next(bp)) {
            totalFreeInLists++;
        }
        
        if(offsetFromPrologue(bp) < 0 ||
        offsetFromPrologue((getNextWord(bp))) < 0) {
        printf("Next or previous address points to somewhere outside the heap");
        printf("Checked in line Number %d",lineNumber);
        exit(0);
        }
        
        if(bp != heap_listp && GET_ALLOC(FTRP(bp))) {
            printf("Error allocated block in free listn");
            printf("Checked in line Number %d",lineNumber);
            exit(0);
        }
        if( bp != heap_listp && next(bp) != heap_listp && bp != prev(next(bp))){
            printf("Points are inconsistentn");
            printf("Checked in line Number %d",lineNumber);
            exit(0);
        }
        
        if(!approrpriateFreeList(GET_SIZE(HDRP(bp))) == start){
            printf("Block is not in the right bucketn");
            printf("Checked in line Number %d",lineNumber);
            exit(0);
        }
        checkblock(bp);
    }
    
    // Number of freebocks in heap and in buckets should be the same
    if(totalFreeInLists != totalFreeInLists){
        printf("Error leaking memory, not keeping track of all free blocksn");
        printf("Checked in line Number %d",lineNumber);
        exit(0);
    }
}