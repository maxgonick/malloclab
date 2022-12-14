/*
 * mm.c -  Simple allocator based on implicit free lists,
 *         first fit placement, and boundary tag coalescing.
 *
 * Each block has header and footer of the form:
 *
 *      63       32   31        1   0
 *      --------------------------------
 *     |   unused   | block_size | a/f |
 *      --------------------------------
 *
 * a/f is 1 iff the block is allocated. The list has the following form:
 *
 * begin                                       end
 * heap                                       heap
 *  ----------------------------------------------
 * | hdr(8:a) | zero or more usr blks | hdr(0:a) |
 *  ----------------------------------------------
 * | prologue |                       | epilogue |
 * | block    |                       | block    |
 *
 * The allocated prologue and epilogue blocks are overhead that
 * eliminate edge conditions during coalescing.
 */
#include "memlib.h"
#include "mm.h"
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Your info */
team_t team = {
    /* First and last name */
    "Maxwell Gonick",
    /* UID */
    "705683791",
    /* Custom message (16 chars) */
    "meep3",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
} header_t;

typedef header_t footer_t;

typedef struct block_t{
    uint32_t allocated : 1;
    uint32_t block_size : 31;
    uint32_t _;
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */
#define MAXBITS (16)

/* Global variables */
//Pointer to pointer to block_t (Making a continguous "array")
static block_t **segListHead;
//Tested and having 11 lists gives good performance as we can stick a lot of the smaller sized blocks in the same list, to reduce fragmentation
static int TOTALNUMLIST = 11;
static block_t *prologue; /* pointer to first block */
// static block_t *head; /* pointer to start of free list */
 
/* function prototypes for internal helper routines */
static int segListIndex(int input);
static block_t *extend_heap(size_t words, bool willCoalesce);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);
static void list_push(block_t *newblock, int index);
static void list_pop(block_t *removeblock, int index);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    //Put pointers to the different seglists at the beginning of the heap
    segListHead = mem_sbrk(sizeof(block_t **) * TOTALNUMLIST);
    //Set all the pointers to NULL to avoid garbages
    for(int i = 0; i < TOTALNUMLIST; i++){
        segListHead[i] = NULL;
    }
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;
    /* initialize the prologue */
    prologue->allocated = ALLOC;
    prologue->block_size = sizeof(header_t);
    /* initialize the first free block */
    block_t *init_block = (void *)prologue + sizeof(header_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD;
    //Setting pointers for explicit free
    init_block->body.next = NULL;
    init_block->body.prev = NULL;
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;
    /* Put last seglist on first free block */
    segListHead[TOTALNUMLIST - 1] = init_block;
    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;
    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    //Optimization that improves performance by automatically extending heap for small malloc() calls
    if (asize <= 96){
        extendsize = asize;
        extendwords = extendsize >> 3;
       block = extend_heap(extendwords, false );
        if(block != NULL){

            place(block,asize);
            return block->body.payload;
        }
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        place(block, asize);
        return block->body.payload;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                     ? asize
                     : CHUNKSIZE;
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords, true)) != NULL) {
        place(block, asize);
        return block->body.payload;
    }
    /* no more memory :( */
    return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block
 */
/* $begin mmfree */
void mm_free(void *payload) {
    //pointer to front of allocated block
    block_t *block = payload - sizeof(header_t);
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;
    int freeIndex = segListIndex(block->block_size);
    list_push(block, freeIndex);
    coalesce(block);

}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
    void *newp;
    size_t copySize;

    if ((newp = mm_malloc(size)) == NULL) {
        printf("ERROR: mm_malloc failed in mm_realloc\n");
        exit(1);
    }
    block_t* block = ptr - sizeof(header_t);
    copySize = block->block_size;
    if (size < copySize)
        copySize = size;
    memcpy(newp, ptr, copySize);
    mm_free(ptr);
    return newp;
}

/*
 * mm_checkheap - Check the heap for consistency
 */
void mm_checkheap(int verbose) {
    block_t *block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    if (block->block_size != sizeof(header_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue+prologue->block_size; block->block_size > 0; block = (void *)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

static inline int logBaseTwo(int input){ 
    return 31 - __builtin_clz(input);
}

static int segListIndex(int input){
    //Blocks will be sent to lists depending on size (with a bias of -5, so smaller size blocks will all together (consequence of 2^n function starting slow and jumping up quickly))
    int index = logBaseTwo(input) - 5;
    //Put bounds on the index such that that maximum block sizes are restricted to a specific index of TOTALNUMLSIT - 5
    return (index < (TOTALNUMLIST - 1)) ? index : (TOTALNUMLIST - 1);
}

// Adding newly freed block onto linked list
static void list_push(block_t *newblock, int index){
    
    //If list is empty
    if(segListHead[index] == NULL){
       segListHead[index] = newblock; 
       newblock->body.prev = NULL;
       newblock->body.next = NULL;
    }
    else{
        //Setting up newblock pointers
    newblock->body.next = segListHead[index];
    newblock->body.prev = NULL; 
    segListHead[index]->body.prev = newblock;
    segListHead[index] = newblock;
    }
    
    return;
}

// Removing free block from list
static void list_pop(block_t *removeblock, int index){

    //Case 1 (Only block in list)
    if(removeblock->body.prev == NULL && removeblock->body.next == NULL){
        segListHead[index] = NULL;
        return;
    }

    //Case 2 (First block in list)
    else if(segListHead[index] == removeblock){
        segListHead[index] = removeblock->body.next;
        removeblock->body.next->body.prev = NULL;

        return;
    }
    //Case 3 (Last block in list)
    else if(removeblock->body.next == NULL){
        removeblock->body.prev->body.next = NULL;

        return;
    }
    //Case 4 (Middle of list)
    else{
        //Set pointers for next block
        removeblock->body.next->body.prev = removeblock->body.prev;
        //Set pointer for previous block
        removeblock->body.prev->body.next = removeblock->body.next;
        //null out removeblock pointer

        return;
    }

}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words, bool willCoalesce) {
    block_t *block;
    uint32_t size;
    size = words << 3; // words*8
    if (size == 0 || (block = mem_sbrk(size)) == (void *)-1)
        return NULL;
    /* The newly acquired region will start directly after the epilogue block */ 
    /* Initialize free block header/footer and the new epilogue header */
    /* use old epilogue as new free block header */
    block = (void *)block - sizeof(header_t);
    block->allocated = FREE;
    block->block_size = size;
    /* free block footer */
    footer_t *block_footer = get_footer(block);
    block_footer->allocated = FREE;
    block_footer->block_size = block->block_size;
    /* new epilogue header */
    header_t *new_epilogue = (void *)block_footer + sizeof(header_t);
    new_epilogue->allocated = ALLOC;
    new_epilogue->block_size = 0;
    /* Coalesce if the previous block was free */
    //Creating new segList block
    int blockIndex = segListIndex(block->block_size);
    list_push(block, blockIndex);
    if(willCoalesce == true){
        return coalesce(block);
    }
    else return block;
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
    size_t split_size = block->block_size - asize;
    if (split_size >= MIN_BLOCK_SIZE) {
        int indexNum = segListIndex(block->block_size);
        //Remove block from free list
        list_pop(block, indexNum);
        /* split the block by updating the header and marking it allocated*/
        block->block_size = asize;
        block->allocated = ALLOC;
        /* set footer of allocated block*/
        footer_t *footer = get_footer(block);
        footer->block_size = asize;
        footer->allocated = ALLOC;
        /* update the header of the new free block */
        block_t *new_block = (void *)block + block->block_size;
        new_block->block_size = split_size;
        new_block->allocated = FREE;
        /* update the footer of the new free block */
        footer_t *new_footer = get_footer(new_block);
        new_footer->block_size = split_size;
        new_footer->allocated = FREE;
        //Add new_block to list
        indexNum = segListIndex(new_block->block_size);
        list_push(new_block, indexNum);
    } else {
        int indexNum = segListIndex(block->block_size);
        list_pop(block, indexNum);
        /* splitting the block will cause a splinter so we just include it in the allocated block */
        block->allocated = ALLOC;
        footer_t *footer = get_footer(block);
        footer->allocated = ALLOC;
    }
}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    block_t *b;
    int sizeIndex = segListIndex(asize);

    //Indexing over different segLists
    for(int i = sizeIndex; i < TOTALNUMLIST; i++){

    //Starting at first block traverse using next pointers
    for (b = segListHead[i]; b != NULL; b = b->body.next) {  //
        /* block must be free and the size must be large enough to hold the request */
        if (!b->allocated && asize <= b->block_size) {
            return b;
        }
    }
}
    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static block_t *coalesce(block_t *block) {
    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;
    block_t *next_block = (void *)next_header;
    block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);

    if (prev_alloc && next_alloc) { /* Case 1 */
        /* no coalesceing */
        return block;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 */
        int coalesceIndex = segListIndex(block->block_size);
        list_pop(block, coalesceIndex);
         coalesceIndex = segListIndex(next_block->block_size);
        list_pop(next_block, coalesceIndex);
        /* Update header of current block o include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;
        //Remove *2nd* part of block from list
        coalesceIndex = segListIndex(block->block_size);
        list_push(block, coalesceIndex);
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 */
        int coalesceIndex = segListIndex(block->block_size);
        list_pop(block, coalesceIndex);
         coalesceIndex = segListIndex(prev_block->block_size);
        list_pop(prev_block, coalesceIndex);
        /* Update header of prev block to include current block's size */
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        block = prev_block;
         coalesceIndex = segListIndex(block->block_size);
        list_push(block, coalesceIndex);
    }

    else { /* Case 4 */
    int coalesceIndex = segListIndex(prev_block->block_size);
        list_pop(prev_block, coalesceIndex);
        coalesceIndex = segListIndex(block->block_size);
        list_pop(block, coalesceIndex);
        coalesceIndex = segListIndex(next_block->block_size);
        list_pop(next_block, coalesceIndex);
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        //Change pointers of list
        block = prev_block;
        coalesceIndex = segListIndex(block->block_size);
        list_push(block, coalesceIndex);
    }
    return block;
}

static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

static void printblock(block_t *block) {
    uint32_t hsize, halloc, fsize, falloc;

    hsize = block->block_size;
    halloc = block->allocated;
    footer_t *footer = get_footer(block);
    fsize = footer->block_size;
    falloc = footer->allocated;

    if (hsize == 0) {
        printf("%p: EOL\n", block);
        return;
    }

    printf("%p: header: [%d:%c] footer: [%d:%c]\n", block, hsize,
           (halloc ? 'a' : 'f'), fsize, (falloc ? 'a' : 'f'));
}

static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
