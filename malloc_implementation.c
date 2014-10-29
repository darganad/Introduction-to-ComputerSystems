/*
 * mm.c
 * adargan - Aditya Dargan
 */

/*
 * 32-bit and 64-bit clean allocator based on explicit free
 * lists, combo of first fit/best fit placement, and boundary tag coalescing
 * Blocks are  aligned to doubleword (8 byte) boundaries. Minimum block size is 24 bytes.
 * A global pointer is used to point to the start of the free block linked list. Blocks
   are added to the front of the list and can be removed from the list as well. 
 *  A free block is encompassed of the following:
  * HEADER - 4 bytes ( size  and allocation state ( 0- free, 1- allocated ))
  * NEXTP- 8 bytes ( contains the address of the next free block)
  * PREVP- 8 bytes ( contains the address of the previous free block)
  * FOOTER- 4 bytes ( size and allocations state)

 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>

#include "mm.h"
#include "memlib.h"
#include <assert.h>
#include "contracts.h"

/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ 
#define DSIZE       8       /* Doubleword size (bytes) */
#define CHUNKSIZE (2048) /* Extend heap by this amount (bytes) */  
//#define CHUNKSIZE (1<<6)

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))           
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   
#define GET_ALLOC(p) (GET(p) & 0x1)                    

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)                     
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

#define GET_NEXT_FREE(bp) ( *(char**) (bp)   )
#define GET_PREV_FREE(bp) ( *(char**) ( (char*)(bp) + DSIZE) )

#define PUT_NEXT_FREE(bp,val) (GET_NEXT_FREE(bp) =(val))
#define PUT_PREV_FREE(bp,val) (GET_PREV_FREE(bp) = (val))



#define HEADER_SIZE 4
#define NEXT_POINTER_SIZE 8
#define PREV_POINTER_SIZE 8
#define FOOTER_SIZE 4
#define ALLOCED 1
#define FREE 0
#define FURTHESTDOWN 200
#define MIN_SIZE 24
#define ALIGN 8
#define FITS 8


#ifdef DRIVER
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif


/* Global variables */
static char *heap_listp = 0;  /* Pointer to first block */

/* points to the start of the free block list */
static void* free_list_root;

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static inline  void add_to_freelist(void* bp);
static inline void remove_from_freelist( void* bp);

/*
 * mm_init - Initialize the memory manager
 */

int mm_init(void)
{
    /* Create the initial empty heap */
    if ( (heap_listp = mem_sbrk(4*WSIZE) ) == (void *)-1) //line:vm:mm:begininit
       return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                     
    free_list_root=NULL;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
       return -1;
    return 0;
}

/*
 * mm_malloc - Allocate a block with at least size bytes of payload
 */
void *mm_malloc(size_t size)
{

    REQUIRES(mm_checkheap(1));
    
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    if (heap_listp == 0){
       mm_init();
    }
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* adjust block to be correctly aligned */

    if( size<= 2*DSIZE){
        asize= 3* DSIZE;
      }
     else
      asize = (2*DSIZE) * ((size + (2*DSIZE) + ((2*DSIZE)-1)) / (2*DSIZE));
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  
       place(bp, asize);                  
       return bp;
    }
    /* No fit found. Get more memory and place the block */      
    extendsize=MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
       return NULL;                                 
    place(bp, asize);       
    ENSURES(mm_checkheap(1));
    return bp;
}


/*


add_to_freelist- add block node to free list. Adds to the front of the list

*/

static inline void add_to_freelist( void *bp){

 REQUIRES(bp!=NULL);
 REQUIRES(mm_checkheap(1));

 //if the free list is empty 
if(free_list_root == NULL){
  free_list_root=bp;
  
  PUT_PREV_FREE(bp,NULL);
  PUT_NEXT_FREE(bp,NULL);
  assert(mm_checkheap(1));
  return; 
}

// if free list is not empty, add the new block to the front of the list
PUT_NEXT_FREE(bp,free_list_root);
PUT_PREV_FREE(bp,NULL);
PUT_PREV_FREE(free_list_root,bp);
free_list_root=bp;
ENSURES(mm_checkheap(1));
return;

}


/*

remove_from_freelist- Remove block from free list. 


*/

static inline void remove_from_freelist( void *bp){

  REQUIRES(bp!=NULL);
  REQUIRES( mm_checkheap(1) );
  
  if( GET_PREV_FREE(bp)== NULL && GET_NEXT_FREE(bp)==NULL){
    free_list_root=NULL;
   
  }
  
// if the block is in the front of the list
  else if (GET_PREV_FREE(bp)==NULL){
    free_list_root= GET_NEXT_FREE(bp);
    PUT_PREV_FREE( free_list_root,NULL);
  } 

// block is at the end of the list
  else if( GET_NEXT_FREE(bp)== NULL){
    PUT_NEXT_FREE(GET_PREV_FREE(bp),NULL);
  }
  else{

// if the block isnt at the front or back of the list
  PUT_NEXT_FREE(GET_PREV_FREE(bp),GET_NEXT_FREE(bp));
  PUT_PREV_FREE(GET_NEXT_FREE(bp), GET_PREV_FREE(bp));
  PUT_PREV_FREE(bp,NULL);
  PUT_NEXT_FREE(bp,NULL);
 

  }
  ENSURES(mm_checkheap(1));
  return;
}

void mm_free(void *bp)
{
    assert(mm_checkheap(1));
    if(bp == 0)
       return;

    size_t size = GET_SIZE(HDRP(bp));
    if (heap_listp == 0){
       mm_init();
    }

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);
    ENSURES(mm_checkheap(1));
    return; 
}


/*

coalesce- Merges together free blocks in the heap
          and puts them in the free list
*/

static void *coalesce(void *bp)
{
    
    REQUIRES(bp!=NULL);
    size_t prev_block_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_block_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    size_t size_to_the_side;

    if( prev_block_alloc && next_block_alloc){
      add_to_freelist(bp);
      ENSURES(mm_checkheap(1));
      return bp;

    }

    /* prev block is free, next isnt */
    else if( !prev_block_alloc && next_block_alloc) 
    {
      
      remove_from_freelist(PREV_BLKP(bp));
      size_to_the_side=size+GET_SIZE(HDRP(PREV_BLKP(bp)));
      PUT(HDRP(PREV_BLKP(bp)), PACK( size_to_the_side,FREE)  );
      PUT(FTRP(bp),PACK(size_to_the_side,FREE));
      add_to_freelist(PREV_BLKP(bp));
      ENSURES(mm_checkheap(1));
      return PREV_BLKP(bp) ;

    }

    /* next block is free, prev block isnt it */
    else if( prev_block_alloc && !next_block_alloc ) 
    {
      
      remove_from_freelist(NEXT_BLKP(bp));
      size_to_the_side= size+ GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size_to_the_side,FREE));
      PUT(HDRP(bp),PACK(size_to_the_side,FREE));
      add_to_freelist(bp);
      ENSURES(mm_checkheap(1));
      return bp;
    }

     /* next block is free and prev block is free */
    else       
    {
      remove_from_freelist(NEXT_BLKP(bp));
      remove_from_freelist(PREV_BLKP(bp));
      size_to_the_side=size+GET_SIZE(HDRP(PREV_BLKP(bp)))+ GET_SIZE(HDRP(NEXT_BLKP(bp)));
      PUT(HDRP(PREV_BLKP(bp)), PACK( size_to_the_side,FREE));
      PUT(FTRP(NEXT_BLKP(bp)), PACK(size_to_the_side,FREE));
      add_to_freelist(PREV_BLKP(bp));
      ENSURES(mm_checkheap(1));
      return PREV_BLKP(bp);
    }
    
    
}

/*
 * mm_realloc - Naive implementation of realloc
 */
void *mm_realloc(void *ptr, size_t size)
{
    REQUIRES(mm_checkheap(1));
    size_t oldsize;
    void *newptr;

    /* If size == 0 then this is just free, and we return NULL. */
    if(size == 0) {
       mm_free(ptr);
       ENSURES(mm_checkheap(1));
       return 0;
    }

    /* If oldptr is NULL, then this is just malloc. */
    if(ptr == NULL) {
      ENSURES(mm_checkheap(1));
       return mm_malloc(size);
    }

    newptr = mm_malloc(size);

    /* If realloc() fails the original block is left untouched  */
    if(!newptr) {
      ENSURES(mm_checkheap(1));
       return 0;
    }

    /* Copy the old data. */
    oldsize = GET_SIZE(HDRP(ptr));
    if(size < oldsize) oldsize = size;
    memcpy(newptr, ptr, oldsize);

    /* Free the old block. */
    mm_free(ptr);
    ENSURES(mm_checkheap(1));
    return newptr;
}


void *mm_calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}


/*
 * checkheap - return 1 if everything in the heap meets invariants, else return 0
 * Checks block alignment, blocks in free list, size of blocks, etc.
 */
int mm_checkheap(int verbose)
{
    
    void * block;
    int i=0;
    int j=0;
    for( block= free_list_root;block != NULL;block = GET_NEXT_FREE(block)   )
    {
        //all pointers are within the range of the heap
       if (!(((long) mem_heap_lo() < (long) block ) && 
            ((long) block < (long ) mem_heap_hi()) )){
          printf("pointer is out of range of the heap\n");
          return 0;
        }

        // check if each block's size in the heap is a multiple of 8
        if (!(( GET_SIZE( HDRP(block)) % ALIGN == 0  )) ){
          printf("block is not aligned\n");
          return 0;
        }

       //check that prev pointers of the next block point to the current block
      if(GET_NEXT_FREE(block)!=NULL){
          if (!( GET_PREV_FREE (block)== NULL || 
        GET_PREV_FREE( GET_NEXT_FREE(block )) == block )) {
          printf("next block's prev pointer doesnt point to current block\n");
          return 0;
          }
     }
        //check no two free blocks are next to each other
      if (NEXT_BLKP(block) !=NULL){
        if (!( GET_ALLOC( HDRP( block)) != GET_ALLOC(HDRP(NEXT_BLKP( block))))){
            printf("two free blocks together in the heap\n");
            return 0;
            }
       }

       //check size is bigger or equal to min size
       if(!(GET_SIZE(HDRP(block))>= (MIN_SIZE))){
          printf("block size is smaller than min size");
          return 0;
       }

         //check sizes are the same in header and footer
      if ( !(GET_SIZE(HDRP(block)) == GET_SIZE(FTRP(block)))){
          printf("sizes in header and footer are not the same\n" );
          return 0;
      }

        //check allocation is the same in header and footer 
      if (!(GET_ALLOC(HDRP(block))== GET_ALLOC(FTRP(block)) )) {
          printf("allocation in header and footer don't match\n");
          return 0;
          }
        i++;
    }
        //check if the number of free blocks matches the number of blocks
        // counted by going through the free list itself
    for(block=heap_listp;block!=NULL; block=NEXT_BLKP(block) ){
      //ensure that all blocks are 8 byte aligned
      if( !(GET_SIZE(HDRP(block)) %8 ==0  )  ){
        printf("block not aligned\n");
        return 0;
      }   
      if( GET_ALLOC(HDRP(block)) == FREE ){
        j++;
      }
    }
    if(!(i==j)){
      printf("# of free blocks in free list != # of free blocks in heap\n");
      return 0;
      }

  verbose = verbose;
  return 1;
}

/*
 * extend_heap - Extend heap with free block and return its block pointer
 */

static void *extend_heap(size_t words)
{
    REQUIRES(mm_checkheap(1));

    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; 
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */   
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */   
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ 

    /* Coalesce if the previous block was free */
    return coalesce(bp);                                          
}


/*
 * place - Place block of asize bytes at start of free block bp
 *         and split if remainder would be at least minimum block size
 */

static void place(void *bp, size_t asize)
  
{
    REQUIRES( bp!=NULL);
    REQUIRES(mm_checkheap(1));   
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (MIN_SIZE)) {
       PUT(HDRP(bp), PACK(asize, 1));
       PUT(FTRP(bp), PACK(asize, 1));
       remove_from_freelist(bp);
       bp = NEXT_BLKP(bp);
       PUT(HDRP(bp), PACK(csize-asize, 0));
       PUT(FTRP(bp), PACK(csize-asize, 0));
       add_to_freelist(bp);
    }
    else {
       PUT(HDRP(bp), PACK(csize, 1));
       PUT(FTRP(bp), PACK(csize, 1));
       remove_from_freelist(bp);
    }
    ENSURES(mm_checkheap(1));
}


/*
 * find_fit - Find a fit for a block with asize bytes. Best fit algorithm- find a block that works, start counting,
    keep looking for the block sizes that are closest to the requested size and return the best block that is found
    when I have gone through a certain number of free blocks or I reach the end of the free list or if I have
    found too many blocks that work
 */

static void *find_fit(size_t asize)
{
  assert(mm_checkheap(1));

  size_t blocksize; 
  size_t best;
  void* block;
  void* bp=NULL;
  int count=0;
  int scount=0;
  int start_counting=0;

  for( block = free_list_root;  block != NULL && count< FITS && scount < FURTHESTDOWN; block = GET_NEXT_FREE(block)   )
  {
    blocksize=GET_SIZE(HDRP(block));
    if(start_counting){
      scount++;
    }
    if( asize<= blocksize){
      count++;
      if(count==1){
        start_counting=1;
        best=blocksize;
        bp=block; 
        }
      if(blocksize< best){
        best=blocksize;
        bp=block;
      }
    }
}
  assert(mm_checkheap(1));
  return bp;
}



