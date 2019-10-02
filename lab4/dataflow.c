#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <pthread.h>
#include "dataflow.h"
#include "error.h"
#include "list.h"
#include "set.h"

typedef struct vertex_t	vertex_t;
typedef struct task_t	task_t;
pthread_mutex_t lock;
 
/* cfg_t: a control flow graph. */
struct cfg_t {
	size_t			nvertex;	/* number of vertices		*/
	size_t			nsymbol;	/* width of bitvectors		*/
	vertex_t*		vertex;		/* array of vertex		*/
};

/* vertex_t: a control flow graph vertex. */
struct vertex_t {
	size_t			index;		/* can be used for debugging	*/
	set_t*			set[NSETS];	/* live in from this vertex	*/
	set_t*			prev;		/* alternating with set[IN]	*/
	size_t			nsucc;		/* number of successor vertices */
	vertex_t**		succ;		/* successor vertices 		*/
	list_t*			pred;		/* predecessor vertices		*/
	pthread_mutex_t mutex;
	bool			listed;		/* on worklist			*/
};

static void clean_vertex(vertex_t* v);
static void init_vertex(vertex_t* v, size_t index, size_t nsymbol, size_t max_succ);

cfg_t* new_cfg(size_t nvertex, size_t nsymbol, size_t max_succ)
{
	size_t		i;
	cfg_t*		cfg;

	cfg = calloc(1, sizeof(cfg_t));
	if (cfg == NULL)
		error("out of memory");

	cfg->nvertex = nvertex;
	cfg->nsymbol = nsymbol;

	cfg->vertex = calloc(nvertex, sizeof(vertex_t));
	if (cfg->vertex == NULL)
		error("out of memory");

	for (i = 0; i < nvertex; i += 1)
		init_vertex(&cfg->vertex[i], i, nsymbol, max_succ);

	return cfg;
}

static void clean_vertex(vertex_t* v)
{
	int		i;

	for (i = 0; i < NSETS; i += 1)
		free_set(v->set[i]);
	free_set(v->prev);
	free(v->succ);
	free_list(&v->pred);
}

static void init_vertex(vertex_t* v, size_t index, size_t nsymbol, size_t max_succ)
{
	int		i;

	v->index	= index;
	v->succ		= calloc(max_succ, sizeof(vertex_t*));
	pthread_mutex_init(&v->mutex, NULL);


	if (v->succ == NULL)
		error("out of memory");
	
	for (i = 0; i < NSETS; i += 1)
		v->set[i] = new_set(nsymbol);

	v->prev = new_set(nsymbol);
}

void free_cfg(cfg_t* cfg)
{
	size_t		i;

	for (i = 0; i < cfg->nvertex; i += 1)
		clean_vertex(&cfg->vertex[i]);
	free(cfg->vertex);
	free(cfg);
}

void connect(cfg_t* cfg, size_t pred, size_t succ)
{
	vertex_t*	u;
	vertex_t*	v;

	u = &cfg->vertex[pred];
	v = &cfg->vertex[succ];

	u->succ[u->nsucc++ ] = v;
	insert_last(&v->pred, u);
}

bool testbit(cfg_t* cfg, size_t v, set_type_t type, size_t index)
{
	return test(cfg->vertex[v].set[type], index);
}

void setbit(cfg_t* cfg, size_t v, set_type_t type, size_t index)
{
	set(cfg->vertex[v].set[type], index);
}

vertex_t* take_first_sync(list_t list){
	vertex_t* u = NULL;
	pthread_mutex_lock(&lock);
	u = remove_first(list);
	pthread_mutex_unlock(&lock);
	return u;
}

void* work(void* list_in)
{
		list_t** worklist = (list_t**)list_in;
		vertex_t*	u;
		vertex_t*	v;
		set_t*		prev;
		size_t		i;
		size_t		j;
		list_t*		p;
		list_t*		h;


		while ((u = take_first_sync(worklist)) != NULL) {
		pthread_mutex_lock(u->mutex);
		u->listed = false;
		reset(u->set[OUT]);
		pthread_mutex_unlock(u->mutex);

		for (j = 0; j < u->nsucc; ++j){
			pthread_mutex_lock(u->succ[j]->mutex);
			or(u->set[OUT], u->set[OUT], u->succ[j]->set[IN]);
			pthread_mutex_unlock(u->succ[j]->mutex);
		}
			
		pthread_mutex_lock(u->mutex);
		prev = u->prev;
		u->prev = u->set[IN];
		u->set[IN] = prev;
		/* in our case liveness information... */
		propagate(u->set[IN], u->set[OUT], u->set[DEF], u->set[USE]);
		pthread_mutex_unlock(u->mutex);

		if (u->pred != NULL && !equal(u->prev, u->set[IN])) {
			p = h = u->pred;
			do {
				v = p->data;
				pthread_mutex_lock(v->mutex);
				if (!v->listed) {
					v->listed = true;
					pthread_mutex_lock(&lock);
					insert_last(worklist, v);
					pthread_mutex_unlock(&lock);

				}
				pthread_mutex_unlock(v->mutex);

				p = p->succ;

				} while (p != h);
			}
		}
	return NULL;
}

void liveness(cfg_t* cfg)
{
	vertex_t*	u;
	list_t*		worklist;
	

	pthread_t	thread[4];
	worklist = NULL;
	pthread_mutex_init(&lock, NULL);

	
	for (i = 0; i < cfg->nvertex; ++i) {
		u = &cfg->vertex[i];
		pthread_mutex_init(&u->lock, NULL);

		insert_last(&worklist, u);
		u->listed = true;
	}


	for(i = 0; i < 4; i += 1){
		pthread_create(&thread[i], NULL, work, &worklist);
	}

	for(i = 0; i < 4; i += 1){
		pthread_join(thread[i], NULL);
	}

}


void print_sets(cfg_t* cfg, FILE *fp)
{
	size_t		i;
	vertex_t*	u;

	for (i = 0; i < cfg->nvertex; ++i) {
		u = &cfg->vertex[i]; 
		fprintf(fp, "use[%zu] = ", u->index);
		print_set(u->set[USE], fp);
		fprintf(fp, "def[%zu] = ", u->index);
		print_set(u->set[DEF], fp);
		fputc('\n', fp);
		fprintf(fp, "in[%zu] = ", u->index);
		print_set(u->set[IN], fp);
		fprintf(fp, "out[%zu] = ", u->index);
		print_set(u->set[OUT], fp);
		fputc('\n', fp);
	}
}
