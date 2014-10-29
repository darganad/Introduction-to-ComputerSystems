#include "csapp.h"
#include "cache.h"




/* Mutexes for thread protection on the cache */
sem_t count_mutex;
sem_t LRU_mutex;
sem_t write_mutex;

static int remaining_cache_size = MAX_CACHE_SIZE;
static int readers_count = 0; //keeps track of clients reading the cache



// Initializes default values in the cache
inline void init_cache(Cache *c)
{
    c->last_access = 0;
    c->url = NULL;
    c->next = NULL;
    c->prev = NULL;
    c->response = NULL;
    c->response_size = 0;
}

/*
 * search_cache - searches the cache with the url provided looking for a hit.
 * If there is a cache hit, we return the cache entry.
 * Otherwise return NULL, indicating a cache miss
 * Follows closely to p. 970 in the book for readers-writers problem
 */
Cache* search_cache(struct Cache *c, char* curl)
{
    Cache *cache_hit = Malloc(sizeof(struct Cache));
    cache_hit = NULL;

    //Wait to increment readers count
    P(&count_mutex);
    readers_count += 1;

    if(readers_count == 1)
        P(&write_mutex);
  
    V(&count_mutex);

    //Ignore linked list header
    c = c -> next;

    while(c != NULL)
    {
        if(!strcmp(curl, c->url)) // Cache hit
        {
            cache_hit = c;
            
            P(&LRU_mutex);
            cache_hit->last_access = time(NULL);
            V(&LRU_mutex);
            
            P(&count_mutex);
            readers_count -= 1;
            if(readers_count == 0)
              V(&write_mutex);
            V(&count_mutex);
            
            return cache_hit;
        }
        else
            c->last_access = time(NULL);
        c = c -> next;
    }


    // Update mutexes and return
    P(&count_mutex);
    readers_count -= 1;
    if(readers_count == 0)// If no one reading, make it available to write
        V(&write_mutex);
    V(&count_mutex);
    return NULL;
}


/*
 * write_to_cache - makes an entry to the cache and inserts it into the linked
 * list. 
 */
void write_to_cache(Cache *c, char *c_url, int obj_size, char *response)
{
    P(&write_mutex);
    char *new_url = Malloc(strlen(c_url) + 1);
    char *new_response = Malloc(obj_size);

    if(remaining_cache_size >= obj_size)  // Enough space left in cache
    {
        Cache *new_block = Malloc(sizeof(struct Cache));

        new_block->response_size = obj_size;

        new_block->url = new_url;
        strcpy(new_block->url, c_url);

        new_block->response = new_response;
        memcpy(new_block->response, response, obj_size);

        new_block->last_access = time(NULL);
        remaining_cache_size -= obj_size;

        add_cache_entry(c, new_block);
    }
    else  //Eviction
    {
        Cache *LRU;
        LRU = find_LRU(c);
        
        // Search for least recently used and remove from the list
        while((LRU->response_size + remaining_cache_size) < obj_size)
        {
            remaining_cache_size += LRU->response_size;
            delete_cache_entry(LRU);
            LRU = find_LRU(c);
        }

        remaining_cache_size += (LRU->response_size - obj_size);
        // Free old entries and create new ones
        Free(LRU->url);
        Free(LRU->response);
        LRU->url = new_url;
        strcpy(LRU->url, c_url);
        LRU->response = new_response;
        memcpy(LRU->response, response, obj_size);
        LRU->response_size = obj_size;
        LRU->last_access = time(NULL);
    }
    V(&write_mutex);
}

/*
 * find_LRU - finds the least recently used block 
 */
Cache *find_LRU(Cache *c)
{
    time_t t = time(NULL);
    Cache *temp = c;
    c = c->next;
    while(c != NULL)
    {
        if(temp->last_access < t)
        {
            t = c->last_access;
            temp = c;
        }
      c = c -> next;
    }
    return temp;
}

/*
 * add_cache_entry - add cache entry new_block to the cache with header block c
 * Adds to the front of the linked list.
 */
void add_cache_entry(Cache *c, Cache *new_block)
{
    if(c->next == NULL)
    {
        c->next = new_block;
        new_block->next = NULL;
        new_block->prev = c;

    }
    else
    {
        new_block->next = c->next;
        new_block->prev = c;
        c->next = new_block;
        new_block->next->prev = new_block;
    }
}
/*
 * delete_cache_entry - deletes cache entry from the list and free its 
 * structure.
 */
void delete_cache_entry(Cache *LRU)
{
    if(LRU->next == NULL)
    {
        LRU->prev->next = NULL;
        LRU->prev = NULL;
        free_cache_entry(LRU);
    }
    else
    {
        LRU->next->prev = LRU->prev;
        LRU->prev->next = LRU->next;
        LRU->next = NULL;
        LRU->prev = NULL;
        free_cache_entry(LRU);
    }

}
/*
 * free_cache_entry - frees all entres in Cache c then frees itself
 */
void free_cache_entry(Cache *c)
{
    free(c->url);
    free(c->response);
    free(c);
}
