/*
* mm.c
*
* NOTE TO STUDENTS: Replace this header comment with your own header
* comment that gives a high level description of your solution.
*/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
* in, remove the #define DEBUG line. */
#define DEBUG
#ifdef DEBUG
# define dbg_//////print(...) //////print(__VA_ARGS__)
#else
# define dbg_//////print(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */
static char *headOfFreeList = 0;
static char *headOfFreeList2 = 0;
static char *headOfFreeList3 = 0;
static char *headOfFreeList4 = 0;
static char *headOfFreeList5 = 0;
static char *headOfFreeList6 = 0;
static char *headOfFreeList7 = 0;


static inline char * freeListStart(int numList) {
    switch(numList)
    {
        case 1:
        return headOfFreeList;
        break;
        case 2 :
        return headOfFreeList2;
        break;
        case 3 :
        return headOfFreeList3;
        break;
        case 4 :
        return headOfFreeList4;
        break;
        case 5 :
        return headOfFreeList5;
        break;
        case 6 :
        return headOfFreeList6;
        break;
        case 7 :
        return headOfFreeList7;
        break;
    }
    return 0;
}

static inline unsigned int approrpriateFreeList(unsigned int asize) {
    if(asize >= 16 && asize<=31){
        //print("1");
        return 1;
    }
    
    if(asize >= 32 && asize<=63){
        //print("2");
        return 2;
    }
    
    if(asize >= 64 && asize <=127){
        //print("3");
        return 3;
    }
    
    if(asize >= 128 && asize <=255){
        //print("4");
        return 4;
    }
    
    if(asize >= 256 && asize <=511){
        //print("5");
        return 5;
    }
    
    if(asize >= 512 && asize <=1023){
        //print("6");
        return 6;
    }
    //print("7");
    return 7;
}




static inline int offsetFromPrologue(void* bp) {
    return ((char*)bp) - heap_listp;
}


/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(p) (((size_t)(p) + (ALIGNMENT-1)) & ~0x7)

/*
GET_ALLOC(FTRP(PREV_BLKP(bp)));
* If NEXT_FIT defined use next fit search, else use first fit search
*/
//#define NEXT_FIT

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE  144  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst

static inline int MAX(int x, int y) {
    return ((x) > (y)? (x) : (y));
}

/* Pack a size and allocated bit into a word */
static inline int PACK(int size, int alloc) {
    return ((size) | (alloc));
} //line:vm:mm:pack

/* Read and write a word at address p */
static inline unsigned int  GET(void * p) {
    return (*(unsigned int *)(p));
}
static inline void PUT(void * p, int val) {
    (*(unsigned int *)(p) = (val));    //line:vm:mm:put
}
/* Read the size and allocated fields from address p */
static inline unsigned int GET_SIZE(void *p) {
    return (GET(p) & ~0x7);
}                 //line:vm:mm:getsize
static inline unsigned int GET_ALLOC(void *p) {
    return (GET(p) & 0x1) ;                   //line:vm:mm:getalloc
}
/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

// Previous block in the freelist
static inline void* prev(void* bp) {
    unsigned int offsetOfPrev = GET(bp);
    void * prevBlock = (void *)((offsetOfPrev) + heap_listp);
    return prevBlock;
}

static inline void* getNextWord(void* bp){
    return (void*)(((char *)(bp)) + WSIZE);
}

// Next block in the freelist
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
} //line:vm:mm:prevblkp
/* $end mallocmacros */

static inline void* listWithBlock(void* bp){
    for(int start = approrpriateFreeList(GET_SIZE(bp)); start<8; start++){
        char* curList = freeListStart(start);
        if(curList == (char*)bp){
            return freeListStart(start);
        }
  }
         return 0;
}


#ifdef NEXT_FIT
static char *rover;           /* Next fit rover */
#endif

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp);
//static void checkheap(int verbose);
//static void checkblock(void *bp);
//static void checkFreeList(int verbose);


/*
* mm_init - Initialize the memory manager
*/
/* $begin mminit */
int mm_init(void)
{
    /* Create the initial empty heap */
    
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) //line:vm:mm:begininit
    return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    
    ////////print("epilogue (%p):n", heap_listp);
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */
    
    //printblock(blah);
    heap_listp += (2 * WSIZE);                   //line:vm:mm:endinit
    /* $end mminit */
    headOfFreeList = heap_listp;
    headOfFreeList2 = heap_listp;
    headOfFreeList3 = heap_listp;
    headOfFreeList4 = heap_listp;
    headOfFreeList5 = heap_listp;
    headOfFreeList6 = heap_listp;
    headOfFreeList7 = heap_listp;
    #ifdef NEXT_FIT
    rover = headOfFreeList;
    #endif
    /* $begin mminit */
    
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    // if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
    //return -1;
    
    //print("Initialized Heap\n");
    return 0;
}
/* $end mminit */

static void addToFront(void* bp, int freeList){
    //print("Before Add to free List\n");
    //checkFreeList(1);
    ////print("Addingn");
    printblock(bp);
    char* castedBp = (char*)(bp);
    // block previous points to the prologue
    PUT(castedBp,0);
    char * curHead = freeListStart(freeList);
    if(curHead == heap_listp) {
        // In this case we make block next point to the epilogue
        //////print("Happens Not Oftenn");
        char * nextWord = getNextWord(castedBp);
        PUT(nextWord,0);
        
    }
    
    else{
        char * nextWord = getNextWord(castedBp);
        // This is the location of the current head of the free list
        // We then make our new head next curHead to the old head;
        PUT(nextWord,offsetFromPrologue(curHead));
        
        // Make old head previous point to new head with offset;
        
        // This line is causing problems, might want to find out why later.
        PUT(curHead,offsetFromPrologue(castedBp));
    }
    // new head is now the head of the list;
    
    
    if(curHead == headOfFreeList)
    headOfFreeList = castedBp;
    
    if(curHead == headOfFreeList2)
    headOfFreeList2 = castedBp;
    
    if(curHead == headOfFreeList3)
    headOfFreeList3 = castedBp;
    
    if(curHead == headOfFreeList4)
    headOfFreeList4 = castedBp;
    
    if(curHead == headOfFreeList5)
    headOfFreeList5 = castedBp;
    
    if(curHead == headOfFreeList6)
    headOfFreeList6 = castedBp;
    
    if(curHead == headOfFreeList7)
    headOfFreeList7 = castedBp;
    
    
    ////print("Added To Front Of Free Listn");
    //  checkFreeList(1);
}

static void deleteFromFreeList(void* bp){
    //print("Before Deleten");
    //checkFreeList(1);
    ////print("Block that I am deleting n");
    printblock(bp);
    
    char* castedBp = (char*)(bp);
    char * curHead = 0;
    char * oldHead = 0;
    
    char * prevBlockInFreeList = (char*)((prev(castedBp)));
    char * nextBlockInFreeList = (char*)((next(castedBp)));
    
    // Free List is now empty so the head of the freelist just points to the prologue
    if(prevBlockInFreeList != heap_listp && nextBlockInFreeList != heap_listp){
        
        // preddessor block now points to the deleted blocks successor;
        //////print("Two blocks adjacentn");
        #ifdef NEXT_FIT
        if(rover == castedBp){
            rover = prevBlockInFreeList;
        }
        #endif
        PUT(getNextWord(prevBlockInFreeList),offsetFromPrologue(nextBlockInFreeList));
        // successor block now points back to deleted blocks preddessor;
        PUT(nextBlockInFreeList,offsetFromPrologue(prevBlockInFreeList));
        return;
        
        
        //////print("Free List Empty n");
    }
    
    else if(prevBlockInFreeList == heap_listp && nextBlockInFreeList == heap_listp) {
        oldHead = (char*)listWithBlock(bp);
        curHead = heap_listp;
        #ifdef NEXT_FIT
        rover = heap_listp;
        #endif
    }
    else if(nextBlockInFreeList == heap_listp){
        // in this case previous block now points to end
        //////print("Epilogue Case n");
        #ifdef NEXT_FIT
        if(rover == castedBp){
            rover = prevBlockInFreeList;
        }
        #endif
        PUT(getNextWord(prevBlockInFreeList),0);
        return;
    }
    
    else {
        //////print("Prologue Case n");
        // In this case we are deleting the front of the freelist so
        // our successor block now points to the prologue and is the head of the free list
        #ifdef NEXT_FIT
        if(rover == castedBp){
            rover = nextBlockInFreeList;
        }
        #endif
        
        PUT(nextBlockInFreeList,0);
        oldHead = (char*)listWithBlock(bp);
        curHead = nextBlockInFreeList;
    }
    
    if(oldHead == headOfFreeList)
    headOfFreeList = curHead;
    
    if(oldHead == headOfFreeList2)
    headOfFreeList2 = curHead;
    
    if(oldHead == headOfFreeList3)
    headOfFreeList3 = curHead;
    
    if(oldHead == headOfFreeList4)
    headOfFreeList4 = curHead;
    
    if(oldHead == headOfFreeList5)
    headOfFreeList5 = curHead;
    
    if(oldHead == headOfFreeList6)
    headOfFreeList6 = curHead;
    
    if(oldHead == headOfFreeList7)
    headOfFreeList7 = curHead;
    ////print("Deleted From Free List n");
    //checkFreeList(1);
    
}

/*
* mm_malloc - Allocate a block with at least size bytes of payload
*/
/* $begin mmmalloc */
void *mm_malloc(size_t size)
{
    //print("Mallocing\n");
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;
    
    /* $end mmmalloc */
    if (heap_listp == 0) {
        mm_init();
    }
    /* $begin mmmalloc */
    /* Ignore spurious requests */
    if (size == 0)
    return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE) {                                         //line:vm:mm:sizeadjust1
        asize = 2*DSIZE;
    }                                      //line:vm:mm:sizeadjust2
    else{
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE); //line:vm:mm:sizeadjust3
    }
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //line:vm:mm:findfitcall
        place(bp, asize);                  //line:vm:mm:findfitplace
        return bp;
    }
    
    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                //line:vm:mm:growheap1
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
    return NULL;                                  //line:vm:mm:growheap2
    place(bp, asize);
    //////print("Finished Mallocingn");                             //line:vm:mm:growheap3
    return bp;
}
/* $end mmmalloc */

/*
* mm_free - Free a block
*/
/* $begin mmfree */
void mm_free(void *bp)
{
    //print("Freeing\n");
    /* $end mmfree */
    if (bp == 0)
    return;
    
    /* $begin mmfree */
    size_t size = GET_SIZE(HDRP(bp));
    /* $end mmfree */
    if (heap_listp == 0) {
        mm_init();
    }
    /* $begin mmfree */
    
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    void* coalasced = coalesce(bp);
   // printf("size is %u \n",GET_SIZE(bp));
    addToFront(coalasced,approrpriateFreeList(GET_SIZE(HDRP(coalasced))));
    //addToFront(bp);
    //////print("Finished Freeingn");
}

/* $end mmfree */

// coalesce - Boundary tag coalescing. Return ptr to coalesced block

/* $begin mmfree */

static void *coalesce(void *bp)
{
    //print("coalescing\n");
    void* prevBlock = PREV_BLKP(bp);
    void* nextBlock = NEXT_BLKP(bp);
    
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    
    if (prev_alloc && next_alloc) {            // Case 1 //
        return bp;
    }
    
    else if (prev_alloc && !next_alloc) {      // Case 2 //
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
        
        deleteFromFreeList(nextBlock);
    }
    
    else if (!prev_alloc && next_alloc) {      // Case 3 //
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
        deleteFromFreeList(prevBlock);
    }
    
    else {                                     // Case 4 //
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
        GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
        
        deleteFromFreeList(prevBlock);
        deleteFromFreeList(nextBlock);
    }
    // $end mmfree //
    #ifdef NEXT_FIT
    // Make sure the rover isn't pointing into the free block //
    // that we just coalesced //
    if ((rover > (char *)bp) && (rover < (char *)NEXT_BLKP(bp))){
        rover = bp;
        ////print("that thingn");
    }
    #endif
    // $begin mmfree //
    return bp;
}
// $end mmfree //


// mm_realloc - Naive implementation of realloc

void *mm_realloc(void *ptr, size_t size)
{
    //////print("Reallocingn");
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
    //////print("Finished reallocingn");
    return newptr;
}


/*
// checkheap - We don't check anything right now.
*/
void mm_checkheap(int verbose)
{
    verbose = verbose;
}


/*
* The remaining routines are internal helper routines
*/

/*
* extend_heap - Extend heap with free block and return its block pointer
*/
/* $begin mmextendheap */
static void *extend_heap(size_t words)
{
    //print("Extending Heap\n");
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; //line:vm:mm:beginextend
    if ((long)(bp = mem_sbrk(size)) == -1)
    return NULL;                                        //line:vm:mm:endextend
    
    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   //line:vm:mm:freeblockhdr
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   //line:vm:mm:freeblockftr
    //PUT(bp,5);                              /* Insert Prev Free Block offset */
    //char * nextBlock = ((char *)(bp)) + WSIZE;
    //PUT(nextBlock,5);      /* Where we store the next free block offset */
    
    
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ //line:vm:mm:newepihdr
    
    /* Coalesce if the previous block was free */
    void* coalasced = coalesce(bp);
        //print("finished coalescing\n");

    addToFront(coalasced,approrpriateFreeList(GET_SIZE(HDRP(coalasced))));
    // addToFront(bp);
    //checkFreeList(1);
    //////print("Finished Extending Heapn");
    return coalasced;                               //line:vm:mm:returnblock
}
/* $end mmextendheap */

/*
* place - Place block of asize bytes at start of free block bp
*         and split if remainder would be at least minimum block size
*/
/* $begin mmplace */
/* $begin mmplace-proto */
static void place(void *bp, size_t asize)
/* $end mmplace-proto */
{
    //print("Placing\n");
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (2 * DSIZE)) {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        deleteFromFreeList(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        //print("splitting\n");
        addToFront(bp,approrpriateFreeList(GET_SIZE(HDRP(bp))));
        
        // checkFreeList(1);
    }
    else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        deleteFromFreeList(bp);
        // checkFreeList(1);
    }
    //print("Finished Placing\n");
}
/* $end mmplace */

/*
* find_fit - Find a fit for a block with asize bytes
*/
/* $begin mmfirstfit */
/* $begin mmfirstfit-proto */
static void *find_fit(size_t asize)
/* $end mmfirstfit-proto */
{
    //print("Finding Fit\n");
    /* $end mmfirstfit */
    
    #ifdef NEXT_FIT
    /* Next fit search */
    char *oldrover = rover;
    // ////print("POKOP");
    /* Search from the rover to the end of list */
    for ( ; ((char *)(rover))!=heap_listp; rover = next(rover))
    if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
    return rover;
    
    /* search from start of list to old rover */
    for (rover = headOfFreeList; rover!= oldrover; rover = next(rover))
    if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
    return rover;
    
    return NULL;  /* no fit found */
    #else
    /* $begin mmfirstfit */
    /* First fit search */
    void *bp;
    for(int start = approrpriateFreeList(asize); start<8; start++){
        for (bp = freeListStart(start); bp && ((char *)(bp))!=heap_listp; bp = next(bp)) {
            if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
                //    deleteFromFreeList(bp);
                //     checkFreeList(1);
                //print("Finished finding fit\n");
                return bp;
            }
        }
    }
    
    
    
    return NULL; /* No fit */
    /* $end mmfirstfit */
    #endif
}

static void printblock(void *bp)
{
    size_t hsize, halloc, fsize, falloc;
    
    // checkheap(0);
    hsize = GET_SIZE(HDRP(bp));
    hsize = hsize;
    halloc = GET_ALLOC(HDRP(bp));
    halloc = halloc;
    fsize = GET_SIZE(FTRP(bp));
    fsize = fsize;
    falloc = GET_ALLOC(FTRP(bp));
    falloc = falloc;
    
    
    if (hsize == 0) {
        ////print("%p: EOLn %zu", bp,halloc);
        return;
    }
    //  //////print("Address (%p):nn", bp);
    ////print("Header Size %zu, Header Allocated %zu, Footer Size %zu, Footer Allocated %zun", hsize, halloc, fsize, falloc);
    //    //////print("%p: header: [%p:%c] footer: [%p:%c]n", bp,
    //    hsize, (halloc ? 'a' : 'f'),
    //    fsize, (falloc ? 'a' : 'f'));
}

/*
static void checkblock(void *bp)
{
    if ((size_t)bp % 8){
        ////print("Error: %p is not doubleword alignedn", bp);
    }
    if (GET(HDRP(bp)) != GET(FTRP(bp))){
        ////print("Error: header does not match footern");
    }
    
}
*/

/*
void checkFreeList(int verbose){
    char *bp = heap_listp;
    
    //  if (verbose)
    // //////print("Heap (%p):n", heap_listp);
    
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    //////print("Bad prologue headern");
    checkblock(heap_listp);
    
    for (bp = headOfFreeList; bp!=heap_listp; bp = next(bp)) {
        if (verbose)
        printblock(bp);
        checkblock(bp);
    }
    
    // if (verbose)
    // printblock(bp);
    //if (bp == heap_listp){
        ////////print("Actually went to backn");
    //}
}
*/

/*
* checkheap - Minimal check of the heap for consistency

void checkheap(int verbose)
{
    char *bp = heap_listp;
    
    if (verbose)
    //////print("Heap (%p):n", heap_listp);
    
    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp)))
    //////print("Bad prologue headern");
    checkblock(heap_listp);
    
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose)
        printblock(bp);
        checkblock(bp);
    }
    
    if (verbose)
    printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
    //////print("Bad epilogue headern");
}
*/





// Return whether the pointer is in the heap.
// May be useful for debugging.

//static int in_heap(const void *p) {
    //    return p <= mem_heap_hi() && p >= mem_heap_lo();
//}



//  Return whether the pointer is aligned.
//  May be useful for debugging.

//static int aligned(const void *p) {
    //    return (size_t)ALIGN(p) == (size_t)p;
//}