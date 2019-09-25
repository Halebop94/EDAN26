#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdint.h>
#include <sys/time.h>
#include <unistd.h>

#define	WIDTH			(14)		/* text width. */
#define	START_BALANCE		(1000)		/* initial amount in each account. */
#define	ACCOUNTS		(1000)		/* number of accounts. */
#define	TRANSACTIONS		(100000)	/* number of swish transaction to do. */
#define	THREADS			(10)		/* number of threads. */
#define	PROCESSING		(100000)		/* amount of work per transaction. */
#define	MAX_AMOUNT		(100)		/* swish limit in one transaction. */

typedef struct {
	int		balance;
	pthread_mutex_t lock;
	pthread_mutexattr_t attr;
} account_t;

account_t		account[ACCOUNTS];
char*			progname;

double sec(void)
{
	struct timeval  tv;

	gettimeofday(&tv, NULL);

	return tv.tv_sec + 1e-6 * tv.tv_usec;
}

void error(char* fmt, ...)
{
	va_list	ap;

	va_start(ap, fmt);

	fprintf(stderr, "%s: error: ", progname);
	vfprintf(stderr, fmt, ap);
	fputc('\n', stderr);

	va_end(ap);

	exit(EXIT_FAILURE);
}

void extra_processing()
{
	volatile int	i;

	for (i = 0; i < PROCESSING; i += 1)
		;
}

void swish(account_t* from, account_t* to, int amount)
{

  if(from < to){
		pthread_mutex_lock(&from->lock);
		pthread_mutex_lock(&to->lock);}
	else {
		pthread_mutex_lock(&to->lock);
		pthread_mutex_lock(&from->lock);
	}

	if (from->balance - amount >= 0) {

		extra_processing();

		from->balance -= amount;
		to->balance += amount;
	}

	if(from < to) {
		pthread_mutex_unlock(&from->lock);
		pthread_mutex_unlock(&to->lock);
	}else {
		pthread_mutex_unlock(&to->lock);
		pthread_mutex_unlock(&from->lock);
	}
}

void* work(void* p)
{
	int		i;
	int		j;
	int		k;
	int		a;


	for (i = 0; i < TRANSACTIONS / THREADS; i += 1) {

		j = rand() % ACCOUNTS;
		a = rand() % MAX_AMOUNT;
		k = rand() % ACCOUNTS;
		swish(&account[j], &account[k], a);

	}
	return NULL;
}


int main(int argc, char** argv)
{
	int		i;
	int		result;
	uint64_t	total;
	pthread_t	thread[THREADS];
	double		begin;
	double		end;

	printf("swish lab computing transactions per second\n\n");
	printf("%-*s %d\n", WIDTH, "accounts", ACCOUNTS);
	printf("%-*s %d\n", WIDTH, "transactions", TRANSACTIONS);
	printf("%-*s %d\n", WIDTH, "threads", THREADS);
	printf("%-*s %d\n", WIDTH, "processing", PROCESSING);
	printf("\n");

	begin = sec();

	progname = argv[0];

	for (i = 0; i < ACCOUNTS; i += 1){
		account[i].balance = START_BALANCE;
		pthread_mutexattr_init(&account[i].attr);
		pthread_mutexattr_settype(&account[i].attr, PTHREAD_MUTEX_RECURSIVE);
		pthread_mutex_init(&account[i].lock, &account[i].attr);
	}

	for(i = 0; i < THREADS; i += 1){
		pthread_create(&thread[i], NULL, work, NULL);
	}

	for(i = 0; i < THREADS; i += 1){
		pthread_join(thread[i], NULL);
	}

	total = 0;

	for (total = i = 0; i < ACCOUNTS; i += 1)
		total += account[i].balance;

	if (total == ACCOUNTS * START_BALANCE)
		printf("PASS\n\n");
	else
		error("total is %llu but should be %llu\n", total, (uint64_t) ACCOUNTS * START_BALANCE);

	end = sec();

	printf("%-*s %1.3lf s\n", WIDTH, "time", end-begin);
	printf("%-*s %1.1lf s\n", WIDTH, "tps", TRANSACTIONS/(end-begin));
}
