/*
 * mm.c -  The structure of the free blocks is a segregated free list,
 *         containing a total of 22 lists, implemented as explicit lists
 *         and as null terminated, doubly linked lists. 
 *         The free and allocated blocks are linked via an implicit list.
 *         The allocator manipulates the free list through first fit 
 *         placement/class sizes, and boundary tag coalescing. It accesses each 
 *         block using the block_t struct. When freeing, it pushes blocks on 
 *         the segregated list using class sizes and the LIFO policy. When 
 *         allocating, it pops those blocks from the list.
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
    "Lauren Bridgwater",
    /* UID */
    "905759596",
    /* Custom message (16 chars) */
    "Almost there! :)",
};

typedef struct {
    uint32_t allocated : 1;
    uint32_t block_size : 31;    
    uint32_t _;
} header_t;

typedef header_t footer_t;  

typedef struct block_t {
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
#define LOG2(i) 31 - __builtin_clz(i)

/* Global variables */
static block_t *prologue; /* pointer to first block */	
static block_t **seg_list;
static uint32_t TOT_SEG_LISTS = 22;

/* function prototypes for internal helper routines */
static inline uint32_t which_seg_list(uint32_t block_size);
static inline void push(block_t *block, uint32_t segListIndex);
static inline void pop(block_t *block, uint32_t segListIndex);

static inline void mm_checkheap(int verbose);
static inline block_t *extend_heap(size_t words, bool coalBool);
static inline void place(block_t *block, size_t asize);
static inline block_t *find_fit(size_t asize);
static inline block_t *coalesce(block_t *block);
static inline footer_t *get_footer(block_t *block);
static inline void printblock(block_t *block);
static inline void checkblock(block_t *block);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
    /* Initialize which_seg_list */
    seg_list = mem_sbrk(8 * TOT_SEG_LISTS);
    for (uint32_t i = 0; i < TOT_SEG_LISTS; i++)
    {
        seg_list[i] = NULL;
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
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;

    /* 
    *  initialize the next/prev pointers for first block and 
    *  set up seg_list[10] with init_block 
    */
    init_block->body.next = NULL;      // null terminated
    init_block->body.prev = NULL;   
    seg_list[TOT_SEG_LISTS - 1] = init_block;

    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;

    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
            - when allocate, reduce appropriate seg list by popping (within place fxn)
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;


    /* Ignore spurious requests */
    if (size == 0) 
    {
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */
    
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    // With small blocks, directly extend heap
    if (asize <= 64)
    {
        extendwords = asize >> 3;
        if ((block = extend_heap(extendwords, false)) != NULL)
        {
            place(block, asize);
            return block->body.payload;
        }
    }

    /* Search the seg free list for a fit */
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
 * mm_free - Free a block and push it on appropriate segregated explicit list and then coalesce
 */
/* $begin mmfree */
void mm_free(void *payload) {
    block_t *block = payload - sizeof(header_t);  
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;
    uint32_t index = which_seg_list(block->block_size);
    push(block, index);        
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
        printf("    ERROR: mm_malloc failed in mm_realloc\n");
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
void mm_checkheap(int verbose) 
{
    block_t *block = prologue;

    if (verbose)
        printf("Heap (%p):\n", prologue);

    /* if we have a bad prologue header */
    if (block->block_size != sizeof(header_t) || !block->allocated)
        printf("Bad prologue header\n");
    checkblock(prologue);

    /* iterate through the heap (both free and allocated blocks will be present) */
    for (block = (void*)prologue+prologue->block_size; block->block_size > 0; block = (void *)block + block->block_size) {
        if (verbose)
            printblock(block);
        checkblock(block);

        /* check coalescing: make sure no two blocks next to each other are zero */
        if (block->allocated == FREE && (block->body.next)->allocated == FREE)
        {
            printf("Addr: %p - **Coalescing Error** \n", block);
            assert(0);
        }
    }

    /* iterate through seg free list and make sure they are all free */
    int it = 0;
    while (it < TOT_SEG_LISTS)
    {
        int counter = 0;
        for (block = seg_list[it]; block != NULL; block = block->body.next)
        {
            if (block->allocated != FREE)
            {
                printf("Block number %d is not free \n", counter);
            }
        }
        it++;
    }

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/* which_seg_list - determine which seg list the block belongs in*/ 
static uint32_t which_seg_list(uint32_t block_size)
{
    // every block with size less than 256 has its own list (every 8 bytes)
    if (block_size < 256)
    {
        double divisor = 16;
        return ((uint32_t)((block_size - 32) / divisor));
    }
    uint32_t preIndex = LOG2(block_size) - 5;
    if (preIndex < 10)
    {
        return (preIndex + 11);
    }
    return 21;
}

/*
* push - push a block onto the front of appropriate seg explicit list 
         by updating next, prev, and head ptrs, using LIFO policy
*/
static void push(block_t *block, uint32_t segListIndex)
{
   /* push onto list using LIFO policy*/
    if (seg_list[segListIndex] == NULL)    // if explicit list is empty
    {
        block->body.prev = NULL;
        block->body.next = NULL;
        seg_list[segListIndex] = block;
    }
    else
    {
        block->body.prev = NULL;
        block->body.next = seg_list[segListIndex];
        (seg_list[segListIndex])->body.prev = block;
        seg_list[segListIndex] = block;
    }


}

/*
* pop - remove a block from the appropriate seg explicit list by updating
*       next, prev, and head ptrs and accounting for different edge cases
*/
static void pop(block_t *block, uint32_t segListIndex)   
{
    /* edge case - if only one block in list */
    if (block->body.next == NULL && block->body.prev == NULL)   
    {
        seg_list[segListIndex] = NULL;
    }

    /* edge case - segListHead pts to block you are trying to remove */
    else if (block->body.prev == NULL)  // correct way to write this if statement? or should I do if (head == block) or should I do if (*head == *block) 
    {
        seg_list[segListIndex] = block->body.next;
        (seg_list[segListIndex])->body.prev = NULL;
    }

    /* edge case - block points to last block in linked list */
    else if (block->body.next == NULL)     
    {
        block->body.prev->body.next = NULL;
    }

    else // normal case
    {
        block_t *prevBlock = block->body.prev;
        block_t *nextBlock = block->body.next;
        prevBlock->body.next = nextBlock;
        nextBlock->body.prev = prevBlock;
    }
}


/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words, bool coalBool) {
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
    /* push extended free space onto explicit list */
    uint32_t index = which_seg_list(block->block_size);
    push(block, index);    
    /* Coalesce if the previous block was free */
    if (coalBool)
    {
        return coalesce(block);
    }
    return block;
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of appropriate segregated list 
 *         and split if remainder would be at least minimum block size. Push/pop as necessary
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {       // during mm_malloc, the "block" passed here is a ptr to the first block in the list that fit the allocated block
    uint32_t listIndex = which_seg_list(block->block_size);
    size_t split_size = block->block_size - asize;
    if (split_size >= MIN_BLOCK_SIZE) {
        /* split the block by updating the header and marking it allocated*/
        block->block_size = asize;
        block->allocated = ALLOC;
        /* set footer of allocated block*/
        footer_t *footer = get_footer(block);
        footer->block_size = asize;
        footer->allocated = ALLOC;
        /* update the address and header of the new free block */
        block_t *new_block = (void *)block + block->block_size;     // note, by here, block->block_size = asize
        new_block->block_size = split_size;
        new_block->allocated = FREE;
        /* update the footer of the new free block */  
        footer_t *new_footer = get_footer(new_block);
        new_footer->block_size = split_size;
        new_footer->allocated = FREE;
        /* push and pop the free and allocated blocks from explicit list - ADDED */
        uint32_t listIndex = which_seg_list(new_block->block_size);
        push(new_block, listIndex); 
    } else {
        /* splitting the block will cause a splinter so we just include it in the allocated block */
        block->allocated = ALLOC;
        footer_t *footer = get_footer(block);
        footer->allocated = ALLOC;
    }
    
    pop(block, listIndex);

}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes using a first fit placement policy
 *            Use segregated fits approach
 */
static block_t *find_fit(size_t asize) {
    /* first fit search */
    block_t *initFreeB;
    block_t *segListHead;
    uint32_t segListIndex = which_seg_list(asize);

    while (segListIndex < TOT_SEG_LISTS)
    {
    segListHead = seg_list[segListIndex];    // segListHead is ptr to first block in seglist
    for (initFreeB = segListHead; initFreeB != NULL; initFreeB = initFreeB->body.next) 
    {
        if (asize <= initFreeB->block_size)
        {
            return initFreeB;
        }
    }
    segListIndex++;
    }

    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block. 
 *            Coalesce within seg explicit list by popping the two blocks
 *            and then pushing the combo of both to front of list, where appropriate
 */
static block_t *coalesce(block_t *block) {
    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;
    block_t *prev_heap_block = (void *)block - prev_footer->block_size; // could prev/post block ever be null? 
    uint32_t prev_heap_block_index = which_seg_list(prev_heap_block->block_size);
    block_t *next_heap_block = (void *)block + block->block_size;
    uint32_t next_heap_block_index = which_seg_list(next_heap_block->block_size);
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;
    uint32_t block_list_index = which_seg_list(block->block_size);

    if (prev_alloc && next_alloc) { /* Case 1 -> previous and next block are allocated */
        /* no coalesceing */
        return block;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 -> previous is allocated and next is free */
        pop(next_heap_block, next_heap_block_index);            
        pop(block, block_list_index);
        /* Update header of current block to include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;
        /* push the new block onto the explicit list - ADDED */
        uint32_t listIndex = which_seg_list(block->block_size);
        push(block, listIndex);
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 -> previous is free and next is allocated */
        pop(prev_heap_block, prev_heap_block_index);
        pop(block, block_list_index);
        /* Update header of prev block to include current block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        block = prev_block;
        /* push the new block onto the explicit list */
        uint32_t listIndex = which_seg_list(block->block_size);
        push(block, listIndex);
    }

    else /* Case 4 -> previous and free blocks are free */ 
    { 
        /* pop prev_heap_block, next_heap_block, and curr block off explicit list */
        pop(prev_heap_block, prev_heap_block_index);
        pop(next_heap_block, next_heap_block_index);
        pop(block, block_list_index);
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        block = prev_block;
        /* push the new block onto the explicit list */
        uint32_t listIndex = which_seg_list(block->block_size);
        push(block, listIndex);
    }

    return block;
}

/* get_footer - returns a ptr to the footer of block b */
static footer_t* get_footer(block_t *block) {
    return (void*)block + block->block_size - sizeof(footer_t);
}

/* printblock - prints information about the header and footer of block */
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

/* checkblock - makes sure the block is aligned and that the header matches the footer */
static void checkblock(block_t *block) {
    if ((uint64_t)block->body.payload % 8) {
        printf("Error: payload for block at %p is not aligned\n", block);
    }
    footer_t *footer = get_footer(block);
    if (block->block_size != footer->block_size) {
        printf("Error: header does not match footer\n");
    }
}
