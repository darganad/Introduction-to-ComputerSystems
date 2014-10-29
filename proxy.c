/*
 * Lucas Bruder - lbruder
 * Aditya Dargan- adargan
 *
 * This is the concurrent version of proxylab. It implements a doubly linked 
 * list for the cache for fast access to recently retrieved items.
 *
 * Eviction policy for the cache is LRU.
 *
 * Notes: 
 * - cache.c contains the code for the cache. cache.h is the header file
 * - Modified csapp.c for handling broken pipe errors when reading and writing
 * - Type make into the shell to compile and run ./proxy <port> to have the proxy
 *   listen in on that port number.
 * - Proxy ignores request that aren't GET.
 *
 *
 *
 */


#include <stdio.h>
#include "csapp.h"
#include <stdbool.h>
#include "cache.h"

extern sem_t write_mutex;
extern sem_t LRU_mutex;
extern sem_t count_mutex;

/* Request Headers */
static const char *user_agent_hdr = 
"User-Agent: Mozilla/5.0 (X11; Linux x86_64; rv:10.0.3) Gecko/20120305 Firefox/10.0.3\r\n";
static const char *accept_hdr = 
"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n";
static const char *accept_encoding_hdr = 
"Accept-Encoding: gzip, deflate\r\n";
static const char *connection_hdr =
"Connection: close\r\n";
static const char *proxy_connection_hdr =
"Proxy-Connection: close\r\n";
static const char *http_version_hdr = "HTTP/1.0\r\n";


typedef struct args{
  int fd;
  Cache* c;
}args;


/* Function prototypes */
void handle_request(int fd, Cache *c);
void clienterror(int fd, char *cause, char *errnum, 
                 char *shortmsg, char *longmsg);
int parse_url(char* uri, char *host, char* path, int *port);
void *thread(void *vargp);


int main(int argc, char **argv)
{
    int listenfd;  /* listening file descriptor */
    int port;      /* port to listen to connections */
    struct sockaddr_in clientaddr;
    unsigned clientlen;
    pthread_t tid;
    args *a;  // Struct to send the arguments to the thread

    // Ignore SIGPIPE
    Signal(SIGPIPE, SIG_IGN);

    if(argc != 2)
    {
        printf("User error. Please enter in ./proxy <port> \n");
        exit(1);
    }

    /* Initialize cache */
    Cache* c = Malloc(sizeof(struct Cache));
    init_cache(c);

    /* Initialize mutexes */
    Sem_init(&write_mutex,0,1);
    Sem_init(&LRU_mutex,0,1);
    Sem_init(&count_mutex,0,1);


    /* Get port number */
    port = atoi(argv[1]);

    /* Open listening socket on server side */
    listenfd = Open_listenfd(port);

    while(1)
    {
        /* Malloc args struct, put connecting file descriptor and cache
         * entry into struct and pass it on to function thread 
         */
        a = Malloc(sizeof(struct args));
        clientlen = sizeof(clientaddr);
        a->fd = Accept(listenfd, (SA *)&clientaddr, &clientlen);
        a->c = c;
        Pthread_create(&tid, NULL, thread, (void*)a);

    }

    return 0;
}

/*
 * thread - executes thread routine.
 */
void *thread(void *vargp)
{
    Pthread_detach(pthread_self());

    /* Retrieve connecting file descriptor and cache entry */
    int connfd = ((struct args*)vargp)->fd;
    Cache *c = ((struct args*)vargp)->c;

    Free(vargp);

    handle_request(connfd, c);

    Close(connfd);
    return NULL;
}





/*
 * handle_request - takes care of generating HTTP request, connecting to host,
 * and sending request
 */

void handle_request(int fd, Cache *c)
{
    rio_t rio_client;
    char buf[MAXLINE];            // temporary buffer
    char method[MAXLINE];         // type of request
    char version[MAXLINE];        // version of HTTP
    char uri[MAXLINE];            // uri in GET request
    char host[MAXLINE];           // host to connect to
    char path[MAXLINE];           // pathname on server
    char url[MAXLINE];            // url for cache lookup
    char response[MAXLINE];       
    int port = 80;                // default port for HTTP request

    // booleans for request headesr
    bool has_host = false;
    bool has_accept = false;
    bool has_user_agent = false;
    bool has_accept_encoding = false;
    bool has_connection = false;
    bool has_proxy_connection = false;
    
    int n;
    int response_buf_left = MAX_OBJECT_SIZE;
    Cache *cache_hit;
    int serverfd;

    //buffer where the server response goes
    char *response_buf = Calloc(sizeof(char)*MAX_OBJECT_SIZE, 1);

    /* Read request line and headers */
    Rio_readinitb(&rio_client, fd);
    Rio_readlineb(&rio_client, buf, MAXLINE);
    sscanf(buf, "%s %s %s\n", method, uri, version);

    strcpy(url, uri);

    /* Proxy only handles GET method */
    if(strcasecmp(method, "GET"))
    {
        clienterror(fd, method, "501", "Not Implemented", 
                    "Proxy only implements GET request");
        Free(response_buf);
        return;
    }


    /* Get the host, path, and port to connect to */
    int parse = parse_url(uri, host, path, &port);
    if(parse == -1)
    {
        clienterror(fd, host, "400", "Bad Request",
            "Proxy could not understand the request");
        Free(response_buf);
        return;
    }

    //Search cache for entry based on url
    if((cache_hit = search_cache(c, url)) != NULL)
    {
      Rio_writen(fd, cache_hit->response, cache_hit->response_size);
      Free(response_buf);
      return;
    }



    /* Cache miss. Connect to server */

    if((serverfd = open_clientfd_r(host, port)) < 0)
    {
        close(serverfd);
        Free(response_buf);
        return;
    }

    /* Make the request line */
    Rio_writen(serverfd, method, strlen(method));
    Rio_writen(serverfd, " ", strlen(" "));
    Rio_writen(serverfd, path, strlen(path));
    Rio_writen(serverfd, " ", strlen(" "));
    Rio_writen(serverfd, (void*)http_version_hdr, strlen(http_version_hdr));


    /* Parse request and send off immediately */
    while(Rio_readlineb(&rio_client, buf, MAXLINE) > 2){
        if(strstr(buf, "Host: ") != NULL)
        {
            has_host = true;
            Rio_writen(serverfd, buf, strlen(buf));
        }

        else if(strstr(buf, "Accept: ") != NULL)
        {
            has_accept = true;
            Rio_writen(serverfd, (void*)accept_hdr, strlen(accept_hdr)); 
        }
         else if(strstr(buf,"Accept-Encoding: ") != NULL)
        {
            has_accept_encoding = true;
            Rio_writen(serverfd, (void*)accept_encoding_hdr, strlen(accept_encoding_hdr)); 

        }
        else if(strstr(buf, "Connection: ") != NULL)
        {
            has_connection = true;
            Rio_writen(serverfd, (void*)connection_hdr, strlen(connection_hdr)); 

        }
        else if(strstr(buf, "User-Agent: ") != NULL)
        {
            has_user_agent = true;
            Rio_writen(serverfd, (void*)user_agent_hdr, strlen(user_agent_hdr)); 

        }
        else if(strstr(buf, "Proxy-Connection: ") != NULL)
        {
            has_proxy_connection = true;
            Rio_writen(serverfd, (void*)proxy_connection_hdr, strlen(proxy_connection_hdr)); 

        }
         else if((strstr(buf, "User-Agent: ") == NULL)      &&
               (strstr(buf, "Accept-Encoding: ") == NULL)  &&
               (strstr(buf, "Accept: ") == NULL)           &&
               (strstr(buf, "Connection: ") == NULL)       &&
               (strstr(buf, "Proxy Connection: ") == NULL))
        {
            Rio_writen(serverfd, buf, strlen(buf)); 
        }
        
    }



    /*
     * Take care of default headers not included.
     */
    if(!has_host)
    {
        Rio_writen(serverfd, "Host: ", strlen("Host: "));
        Rio_writen(serverfd, host, strlen(host));
        Rio_writen(serverfd, "\r\n", strlen("\r\n"));
    }
    if(!has_accept)
    {
        Rio_writen(serverfd, (void*)accept_hdr, strlen(accept_hdr));
    }
    if(!has_accept_encoding)
    {
        Rio_writen(serverfd, (void*)accept_encoding_hdr, strlen(accept_encoding_hdr));
    }
    if(!has_connection)
    {
        Rio_writen(serverfd, (void*)connection_hdr, strlen(connection_hdr));
    }
    if(!has_user_agent)
    {
        Rio_writen(serverfd, (void*)user_agent_hdr, strlen(user_agent_hdr));
    }
    if(!has_proxy_connection)
    {
        Rio_writen(serverfd, (void*)proxy_connection_hdr, strlen(proxy_connection_hdr));
    }

    Rio_writen(serverfd, "\r\n", strlen("\r\n"));

    int sum = 0; //sum to keep track of total response length

    /* Read server response and send it back to client */
    while((n = Rio_readn(serverfd, response, MAXLINE)) > 0)
    {
        if(response_buf_left - n > 0)
        {
            memcpy((response_buf+sum), response, n);
            sum += n;
        }

        Rio_writen(fd, response, n);
        response_buf_left -= n;
    }

    if((response_buf_left >= 0))
    {
        write_to_cache(c, url, sum, response_buf);
    }

    close(serverfd);
    return;
}


/*
 * clienterror - reports errors to client before.
 */
void clienterror(int fd, char *cause, char *errnum, 
                 char *shortmsg, char *longmsg)
{
    char buf[MAXLINE], body[MAXBUF];

    /* Build the HTTP response body */
    sprintf(body, "<html><title>Proxy Server Error</title>");
    sprintf(body, "%s<body bgcolor=""ffffff"">\r\n", body);
    sprintf(body, "%s%s: %s\r\n", body, errnum, shortmsg);
    sprintf(body, "%s<p>%s: %s\r\n", body, longmsg, cause);
    sprintf(body, "%s<hr><em>Lucas Bruder's Proxy Server</em>\r\n", body);

    /* Print the HTTP response */
    sprintf(buf, "HTTP/1.0 %s %s\r\n", errnum, shortmsg);
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-type: text/html\r\n");
    Rio_writen(fd, buf, strlen(buf));
    sprintf(buf, "Content-length: %d\r\n\r\n", (int)strlen(body));
    Rio_writen(fd, buf, strlen(buf));
    Rio_writen(fd, body, strlen(body));

    return;
}

/*
 * parse_url - Parses a URI from an HTTP proxy GET request and
 * retrieves the host, path, and port to connect to. Returns -1 if 
 * there are any problems.
 */

int parse_url(char* uri, char *host, char* path, int *port)
{
    char *host_beg;   //beginning of host
    char *host_end;   //end of host
    int len;          //length of host name
    char *path_beg;   //beginning of path
   
    /* http:// not in the uri, error */
    if(strncasecmp(uri, "http://", 7) != 0)
    {
       host[0] = '\0';
       return -1;
    }

    /* Skips the http:// and goes to the domain */
    host_beg = uri + 7;

    
    host_end = strpbrk(host_beg, " :/\r\n\0");
    len = host_end - host_beg;

    strncpy(host, host_beg, len);
    host[len] = '\0';

    /* Retrieve new port */
    if(*host_end == ':')
      *port = atoi(host_end + 1);

    if((path_beg = strchr(host_beg, '/')) == NULL)
      path[0] = '/';

    else
    {
      strcpy(path, path_beg);
    }
    return 0;
}
