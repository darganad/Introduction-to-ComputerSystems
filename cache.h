#ifndef __CACHE__
#define __CACHE__

#include "csapp.h"

#define MAX_CACHE_SIZE  1049000
#define MAX_OBJECT_SIZE 102400

typedef struct Cache{
    struct Cache* next;
    struct Cache* prev;
    char *url;
    char *response;
    time_t last_access;
    int response_size;
}Cache;


// Cache function prototypes
void init_cache(Cache *c);
Cache *search_cache(Cache *c, char* url);
Cache *find_LRU(Cache *c);
void write_to_cache(Cache *c, char* c_url, int obj_size, char *response);
void free_cache_entry(Cache *c);
void delete_cache_entry(Cache *LRU);
void add_cache_entry(Cache *c, Cache *new_block);


#endif
