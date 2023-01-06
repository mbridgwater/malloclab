/*
 * mm.c -  The structure of the free blocks is a explicit list 
 *         implemented as a null terminated, doubly linked list. 
 *         The free and allocated blocks are linked via an implicit list.
 *         The allocator manipulates the free list through first fit 
 *         placement, and boundary tag coalescing. It accesses each block
 *         using the block_t struct. When freeing, it pushes blocks on 
 *         the explicit list using the LIFO policy. When allocating, it
 *         pops those blocks from the list.
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
    uint32_t block_size : 31;       // block size of payload
    uint32_t _;
} header_t;

typedef header_t footer_t;  

typedef struct block_t {
    uint32_t allocated : 1;		// Q: ask what this means - google c bit fields
    uint32_t block_size : 31;		
    uint32_t _;				// Q: ask what this means - padding
    union {
        struct {
            struct block_t* next;
            struct block_t* prev;
        };
        int payload[0]; 
    } body;
} block_t;          // sizeof(block_t) is 24 bytes

/* This enum can be used to set the allocated bit in the block */
enum block_state { FREE,
                   ALLOC };

#define CHUNKSIZE (1 << 16) /* initial heap size (bytes) */
#define OVERHEAD (sizeof(header_t) + sizeof(footer_t)) /* overhead of the header and footer of an allocated block */
#define MIN_BLOCK_SIZE (32) /* the minimum block size needed to keep in a freelist (header + footer + next pointer + prev pointer) */

/* Global variables */
static block_t *prologue; /* pointer to first block */		// Q: what is static exactly - global variables
static block_t *head;  /* pointer to head of doubly linked explicit list */

// static int NUM_SEG_LISTS = 11;

/* function prototypes for internal helper routines */
static void push(block_t *block);
static void pop(block_t *block);
static block_t *extend_heap(size_t words);
static void place(block_t *block, size_t asize);
static block_t *find_fit(size_t asize);
static block_t *coalesce(block_t *block);
static footer_t *get_footer(block_t *block);
static void printblock(block_t *block);
static void checkblock(block_t *block);

/*
 * mm_init - Initialize the memory manager
 */
/* $begin mminit */
int mm_init(void) {
//    printf("We hit the mm_init fxn \n");   // DEBUGGING
    /* create the initial empty heap */
    if ((prologue = mem_sbrk(CHUNKSIZE)) == (void*)-1)
        return -1;

    /* initialize the prologue */
    prologue->allocated = ALLOC;     // DONT TOUCH
    prologue->block_size = sizeof(header_t);
    
    /* initialize the first free block */
    block_t *init_block = (void *)prologue + sizeof(header_t);
    init_block->allocated = FREE;
    init_block->block_size = CHUNKSIZE - OVERHEAD;
    footer_t *init_footer = get_footer(init_block);
    init_footer->allocated = FREE;
    init_footer->block_size = init_block->block_size;

    /* initialize the doubly linked list from free blocks and initialize the head */        // ADDED
    head = init_block;
    head->body.next = NULL;      // null terminated
    head->body.prev = NULL;   
    // init_block->body.next = init_block;      // CIRCULAR
    // init_block->body.prev = init_block;     // initially, init block points to itself

    /* initialize the epilogue - block size 0 will be used as a terminating condition */
    block_t *epilogue = (void *)init_block + init_block->block_size;
    epilogue->allocated = ALLOC;
    epilogue->block_size = 0;

    return 0;
}
/* $end mminit */

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
            - when allocate, reduce doubly linked list by popping (within place fxn)
 */
/* $begin mmmalloc */
void *mm_malloc(size_t size) {
 //   printf("We hit the mm_malloc fxn \n");   // DEBUGGING
    uint32_t asize;       /* adjusted block size */
    uint32_t extendsize;  /* amount to extend heap if no fit */
    uint32_t extendwords; /* number of words to extend heap if no fit */
    block_t *block;


    /* Ignore spurious requests */
    if (size == 0)  // Q!!! should be this be <= 0 ?
    {
  //      printf("    size is zero\n");
        return NULL;
    }

    /* Adjust block size to include overhead and alignment reqs. */
    size += OVERHEAD;

    asize = ((size + 7) >> 3) << 3; /* align to multiple of 8 */
    
    if (asize < MIN_BLOCK_SIZE) {
        asize = MIN_BLOCK_SIZE;
    }

    /* Search the free list for a fit */
    if ((block = find_fit(asize)) != NULL) {
        place(block, asize);
        // block->body.next->body.prev = block->body.prev;
        // block->body.prev->body.next = block->body.next;
    //    printf("    Done/returning from with mm_malloc fxn\n");     // DEBUGGING
        return block->body.payload;    
    }

    /* No fit found. Get more memory and place the block */
    extendsize = (asize > CHUNKSIZE) // extend by the larger of the two
                     ? asize
                     : CHUNKSIZE;
    extendwords = extendsize >> 3; // extendsize/8
    if ((block = extend_heap(extendwords)) != NULL) {
        place(block, asize);
 //       printf("    Done/returning from with mm_malloc fxn\n");   // DEBUGGING
        return block->body.payload;     // return payload?
    }
    /* no more memory :( */
 //   printf("    Done/returning from with mm_malloc fxn\n");   // DEBUGGING
    return NULL;
}
/* $end mmmalloc */

/*
 * mm_free - Free a block and push it on explicit list and then coalesce
 */
/* $begin mmfree */
void mm_free(void *payload) {
 //   printf("We hit the mm_free fxn \n");   // DEBUGGING

    if (payload == NULL)       // DEBUGGING
    {
        printf("    ERROR: hm, payload ptr is null? \n");
        return;
    }

    block_t *block = payload - sizeof(header_t);  
    block->allocated = FREE;
    footer_t *footer = get_footer(block);
    footer->allocated = FREE;
    push(block);        
    coalesce(block);
}

/* $end mmfree */

/*
 * mm_realloc - naive implementation of mm_realloc
 * NO NEED TO CHANGE THIS CODE!
 */
void *mm_realloc(void *ptr, size_t size) {
     // DEBUGGING  printf("We hit the mm_realloc fxn \n");   // DEBUGGING
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
    printf("We hit mm_checkheap\n");
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

    /* iterate through free list and make sure they are all free */
    int counter = 0;
    for (block = head; block != NULL; head = head->body.next)
    {
        if (block->allocated != FREE)
        {
            printf("Block number %d is not free \n", counter);
        }
        counter++;
    }

        // Q!!! ADD MORE CHECKS HERE FROM SPEC

    if (verbose)
        printblock(block);
    if (block->block_size != 0 || !block->allocated)
        printf("Bad epilogue header\n");
}

/* The remaining routines are internal helper routines */

/*
* push - push a block onto the front of our our explicit list 
         by updating next, prev, and head ptrs
*/
static void push(block_t *block)
{
// DEBUGGING   printf("We hit the push fxn \n");   // DEBUGGING
    /* puesdocode
    *   prev pointer of the pushed block = head->body.prev
    *   next ptr of pushed block = head
    *   head pointer = pushed block
    */
   /* push onto list using LIFO policy*/
    if (head == NULL)    // if explicit list is empty
    {
// DEBUGGING        printf("    We hit the condition that the explicit list is empty\n");
        block->body.prev = NULL;
        block->body.next = NULL;
        head = block;
    }
    else
    {
// DEBUGGING        printf("    We hit else condition \n");
        block->body.prev = NULL;
        block->body.next = head;
        head->body.prev = block;
        head = block;
    }


}

/*
* pop - remove a block from the list by updating next, prev, and
*       head ptrs and accounting for different edge cases
*/
static void pop(block_t *block)   
{
// DEBUGGING    printf("We hit the pop fxn \n");   // DEBUGGING

    // if (block == NULL)
    // {
 //DEBUGGING   //     printf("    ERROR: rut ro, the block you are tring to pop is null, aka doesnt exist\n");
    // }

    // if (head == NULL)   // DEBUGGING
    // {
 // DEBUGGING   //     printf("    ERROR: Uh oh, you are in the pop fxn yet trying to pop from an empty explicit linked list \n");
    // }
    /* edge case - if only one block in list */
    if (head->body.next == NULL && head->body.prev == NULL)   
    {
 // DEBUGGING       printf("    You hit the edge case that there is only one block in list \n"); // DEBUGGING
//         if (block->body.next != NULL || block->body.prev != NULL)    // DEBUGGING
//         {
//              printf("        ERROR: Oh boi. Somethings wrong \n");
//         }
 //       if (head != block)  // Q!!! this the right way to say if head and block dont pt to the same thing?
 //       {
  // DEBUGGING          printf("        ERROR: Hmm it appears that the head isn't pointing to the right block\n");
  //      }  
        head = NULL;
    }

    /* edge case - head pts to block you are trying to remove */
    else if (block->body.prev == NULL)  // correct way to write this if statement? or should I do if (head == block) or should I do if (*head == *block) 
    {
// DEBUGGING        printf("    You hit the edge case that head pts to block you are trying to remove \n"); // DEBUGGING
//        if (head != block)  // this the right way to say if head and block dont pt to the same thing
 //       {
// DEBUGGING            printf("        ERROR: Hmm it appears that the head isn't pointing to the right block\n");
 //       }
        head = block->body.next;
        head->body.prev = NULL;
    }

    /* edge case - block points to last block in linked list */
    else if (block->body.next == NULL)      //Q!!! Make sure has this edge case
    {
// DEBUGGING        printf("    You hit the edge case that the block you are trying to remove is the last in the list \n");
        block_t *prevBlock = block->body.prev;
        prevBlock->body.next = NULL;
    }

    else // normal case
    {
 // DEBUGGING       printf("    You did not hit an edge case \n"); // DEBUGGING
        block_t *prevBlock = block->body.prev;
        block_t *nextBlock = block->body.next;
 //       if (prevBlock == NULL || nextBlock == NULL)
 //       {
 // DEBUGGING           printf("        ERROR: hmmm, one or both of the pointers for this block is null when they shouldn't be\n");
 //       }
        prevBlock->body.next = nextBlock;
        nextBlock->body.prev = prevBlock;
    }
   // printf("    Done with pop fxn \n"); // DEBUGGING
}


/*
 * extend_heap - Extend heap with free block and return its block pointer
 */
/* $begin mmextendheap */
static block_t *extend_heap(size_t words) {
  // DEBUGGING  printf("We hit extend_heap fxn\n");
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
    push(block);    
    /* Coalesce if the previous block was free */
    return coalesce(block);
}
/* $end mmextendheap */

/*
 * place - Place block of asize bytes at start of free block block
 *         and split if remainder would be at least minimum block size. Push/pop as necessary
 */
/* $begin mmplace */
static void place(block_t *block, size_t asize) {
 // DEBUGGING   printf("We hit the place fxn \n");   // DEBUGGING
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
        push(new_block); 
    } else {
        /* splitting the block will cause a splinter so we just include it in the allocated block */
        block->allocated = ALLOC;
        footer_t *footer = get_footer(block);
        footer->allocated = ALLOC;
    }
    
    pop(block);

}
/* $end mmplace */

/*
 * find_fit - Find a fit for a block with asize bytes using a first fit placement policy
 */
static block_t *find_fit(size_t asize) {
// DEBUGGING    printf("We hit the find_fit fxn \n");   // DEBUGGING
    /* first fit search */
    block_t *initFreeB;

    /* edge case - if there are no free blocks left/if explicit list is empty*/
    if (head == NULL)  
    {
// DEBUGGING        printf("    head is null, so no free blocks left aka explicit list empty\n");
        return NULL;
    }

    for (initFreeB = head; initFreeB != NULL; initFreeB = initFreeB->body.next) 
    {
        if (asize <= initFreeB->block_size)
        {
            // if (initFreeB->allocated == ALLOC)  // DEBUGGING
            // {
 //DEBUGGING           //     printf("    ERROR: uh oh, you have an allocated block within your explicit free list \n");
            // }
            return initFreeB;
        }
    }

    return NULL; /* no fit */
}

/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block. 
 *            Coalesce within explicit list by popping the two blocks
 *            and then pushing the combo of both to front of list
 */
static block_t *coalesce(block_t *block) {
// DEBUGGING    printf("We hit the coalesce fxn \n");   // DEBUGGING
    footer_t *prev_footer = (void *)block - sizeof(header_t);
    header_t *next_header = (void *)block + block->block_size;
    block_t *prev_heap_block = (void *)block - prev_footer->block_size; // could prev/post block ever be null? 
    block_t *next_heap_block = (void *)block + block->block_size;
    bool prev_alloc = prev_footer->allocated;
    bool next_alloc = next_header->allocated;

    if (prev_alloc && next_alloc) { /* Case 1 -> previous and next block are allocated */
        /* no coalesceing */
   // DEBUGGING     printf("    You entered case 1 (previous and next block are allocated)\n");
        return block;
    }

    else if (prev_alloc && !next_alloc) { /* Case 2 -> previous is allocated and next is free */
 // DEBUGGING       printf("    You entered case 2 (previous is allocated and next is free)\n");
        /* pop next_heap_block and curr block off explicit list - ADDED */
        // if (next_heap_block->allocated == ALLOC)
        // {
 // DEBUGGING       //     printf("        ERROR: Uh oh, about to try to pop an allocated block off the explicit list\n");
        // }
        pop(next_heap_block);            
        pop(block);
        /* Update header of current block to include next block's size */
        block->block_size += next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(block);
        next_footer->block_size = block->block_size;
        /* push the new block onto the explicit list - ADDED */
        push(block);
    }

    else if (!prev_alloc && next_alloc) { /* Case 3 -> previous is free and next is allocated */
 // DEBUGGING       printf("    You entered case 3 (previous is free and next is allocated)\n");
        /* pop prev_heap_block and curr block off explicit list - ADDED */
        // if (prev_heap_block->allocated == ALLOC)
        // {
  //DEBUGGING      //     printf("        ERROR: Uh oh, about to try to pop an allocated block off the explicit list\n");
        // }
        pop(prev_heap_block);
        pop(block);
        /* Update header of prev block to include current block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size;
        /* Update footer of current block to reflect new size */
        footer_t *footer = get_footer(prev_block);
        footer->block_size = prev_block->block_size;
        block = prev_block;
        /* push the new block onto the explicit list - ADDED */
        push(block);
    }

    else /* Case 4 -> previous and free blocks are free */ 
    { 
  // DEBUGGING      printf("    You entered case 4 (previous and free blocks are free)\n");
        // if (prev_heap_block->allocated == ALLOC || next_heap_block->allocated == ALLOC)
        // {
 //DEBUGGING       //     printf("        ERROR: Uh oh, about to try to pop an allocated block off the explicit list\n");
        // }
        /* pop prev_heap_block, next_heap_block, and curr block off explicit list - ADDED */
        pop(prev_heap_block);
        pop(next_heap_block);
        pop(block);
        /* Update header of prev block to include current and next block's size */
        block_t *prev_block = (void *)prev_footer - prev_footer->block_size + sizeof(header_t);
        prev_block->block_size += block->block_size + next_header->block_size;
        /* Update footer of next block to reflect new size */
        footer_t *next_footer = get_footer(prev_block);
        next_footer->block_size = prev_block->block_size;
        block = prev_block;
        /* push the new block onto the explicit list - ADDED */
        push(block);
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
