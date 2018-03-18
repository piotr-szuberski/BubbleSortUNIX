/**
 * Piotr Szuberski, ps386182
 * Program written for Concurent Programming lecture at University of Warsaw.
 * It has to perform concurrent sorting of int array, size N*2 in UNIX
 * by creating N processes A and N-1 processes B.
 * Processes A(i) compare and swap T[2*i] and T[2*i+1] elements and signalise to
 * processes B(i) and B(i-1) (excluding A(0) and A(N-1)).
 * Processes B(i) compare and swap T[2*i+1] and T[2*i+2] elements and signalise
 * to processes A(i) and A(i+1).
 * The program implements checking whether the array isn't already sorted by
 * counting compares done in every loop processes A and B perform.
 * It slows down program a lot for the pessimistic examples.
 * The program uses unnamed shared memory and semaphores to communicate between
 * processes.
 */

#include <stdio.h>
#include <semaphore.h>
#include <zconf.h>
#include <sys/mman.h>
#include <stdlib.h>
#include <sys/wait.h>

#define A 0
#define B 1
#define STOP 2
#define SWAPS 3

/**
 * @table - pointer to table of ints of size N*2 to be sorted
 * @semaphoresA - table of semaphores of processes A, size N
 * @semaphoresB - table of semaphores of processes B, size N-1
 * @blockerA - semaphore forcing processes A to wait for each other before awakening
 *            processes B
 * @blockerB - semaphore forcing processes B to wait for each other before awakening
 *            processes A
 * @mutex - semaphore protecting the flags value
 * @flags - table of 4 unsigned integers, indexed as follows:
 *   A - counts how many processes A finished comparing
 *   B - counts how many processes B finished comparing
 *   STOP - if != 0 then the table is already sorted
 *   SWAPS - counts how many swaps has been performed in the current loop
 */
struct shared {
    int* table;
    sem_t* semaphoresA;
    sem_t* semaphoresB;
    sem_t* blockerA;
    sem_t* blockerB;
    sem_t* mutex;
    unsigned* flags;
};

void syserr(const char* msg) {
    fprintf(stderr, "%s", msg);
    exit(1);
}

/**
 * Swap function
 * @param x1
 * @param x2
 */
static void swap(int* x1, int* x2) {
    int tmp = *x1;
    *x1 = *x2;
    *x2 = tmp;
}

/**
 * Helper function making it easier to initialize semaphores
 * @param sem
 * @param start_value
 */
static void init_semaphore(sem_t* sem, unsigned start_value) {
    if (sem_init(sem, 1, start_value) == -1)
        syserr("sem_init");
}

/**
 * Helper function making it easier to destroy semaphores
 * @param sem
 */
static void destroy_semaphore(sem_t* sem) {
    if (sem_destroy(sem) == -1)
        syserr("sem_destroy");
}

/**
 * Helper function making it easier to perform P() operation on semaphores
 * @param sem
 */
static void P(sem_t* sem) {
    if (sem_wait(sem))
        syserr("sem_wait");
}

/**
 * Helper function making it easier to perform V() operation on semaphores
 * @param sem
 */
static void V(sem_t* sem) {
    if (sem_post(sem))
        syserr("sem_post");
}

/**
 * Function printing the table
 * @param table - table of ints
 * @param N - table size (doubled N value)
 */
static void print_table(const int* table, unsigned N) {
    unsigned i, size;
    size = N * 2;
    for (i = 0; i < size; ++i)
        printf("%d\n", table[i]);
}

/**
 * Initializes the unnamed shared memory, allocates amount of space needed
 * @param N - pointer to N value
 * @param *size_mem - pointer to variable containing whole size of shared memory
 * @return pointer to the beginning of shared memory array
 */
static void* init_memory(unsigned* N, size_t* size_mem) {
    int fd_memory = -1;
    int flags, prot;
    void* mapped_mem;

    prot = PROT_READ | PROT_WRITE;
    flags = MAP_SHARED | MAP_ANONYMOUS;

    if (scanf("%u", N) == EOF)
        syserr("scanf");

    if (*N < 2)
        syserr("N too low");

    *size_mem  = sizeof(sem_t) * (2 * (*N) + 2) + sizeof(int) * ((*N) * 2 + 4);

    mapped_mem = mmap(NULL, *size_mem, prot, flags, fd_memory, 0);

    if(mapped_mem == MAP_FAILED)
        syserr("mmap");

    return mapped_mem;
}

/**
 * Initializes the structure of pointers to areas of shared memory
 * @param shm - pointer to the initialized structure
 * @param N - N value
 * @param mapped_mem - pointer to the beginning of array of shared memory
 */
static void init_shm(struct shared *shm, unsigned N, void *mapped_mem) {
    unsigned i, size_tab, sizeB;
    size_t dist1 = sizeof(int) * N * 2;
    size_t dist2 = sizeof(sem_t);

    size_tab = N * 2;
    sizeB = N - 1;
    shm->table = (int*) (mapped_mem);
    shm->semaphoresA = (sem_t*) ((char*) mapped_mem + dist1);
    shm->semaphoresB = (sem_t*) ((char*) mapped_mem + dist1 + dist2*N);
    shm->blockerA = (sem_t*) ((char*) mapped_mem + dist1 + dist2*(2*N-1));
    shm->blockerB = (sem_t*) ((char*) mapped_mem + dist1 + dist2*(2*N));
    shm->mutex = (sem_t*) ((char*) mapped_mem + dist1 + dist2*(2*N+1));
    shm->flags = (unsigned*) ((char*) mapped_mem + dist1 + dist2*(2*N+2));


    for (i = 0; i < size_tab; ++i)
        if(scanf("%d", &shm->table[i]) == EOF)
            syserr("scanf");
    for (i = 0; i < N; ++i)
        init_semaphore(&shm->semaphoresA[i], (i == 0 || i == sizeB) ? 1 : 2);
    for (i = 0; i < sizeB; ++i)
        init_semaphore(&shm->semaphoresB[i], 0);

    init_semaphore(shm->blockerA, 0);
    init_semaphore(shm->blockerB, 0);
    init_semaphore(shm->mutex, 1);
    shm->flags[A] = shm->flags[B] = shm->flags[SWAPS] = shm->flags[STOP] = 0;
}

/**
 * Destroys the initialized semaphores in structure shm
 * @param shm - struct with pointers to the shared memory
 */
static void destruct(struct shared* shm, unsigned N) {
    unsigned i, sizeB;

    sizeB = N -1;
    for (i = 0; i < N; ++i)
        destroy_semaphore(&shm->semaphoresA[i]);
    for (i = 0; i < sizeB; ++i)
        destroy_semaphore(&shm->semaphoresB[i]);

    destroy_semaphore(shm->blockerA);
    destroy_semaphore(shm->blockerB);
    destroy_semaphore(shm->mutex);
}

/**
 * Process A, indexed by i, compares i*2 and i*2+1 value of array in shared memory
 * and swaps it if left value is higher.
 * First, the process tries to pass its semaphore.
 * Then, it checks whether the flag[STOP] isn't set to be true value - if so, it
 * awakens the processes B it is connected with.
 * Next, it compares its values and if the swap was executed, increases flag[COMP].
 * After that all processes but not the last one are stopped on stopperA. The
 * last one does V(stopperA) and it is repeated until the last process came
 * across stopperA. The last one opens the mutex.
 * @param shm -structure with pointers to the shared memory
 * @param N - N value
 * @param i - index of the process A
 */
void processA(struct shared* shm, unsigned N, unsigned i) {
    int* table;
    unsigned idxl, idxr;
    sem_t *semA, *semlB, *semrB;

    idxl = i * 2;
    idxr = idxl + 1;
    table = shm->table;
    semA = &shm->semaphoresA[i];
    semrB = &shm->semaphoresB[i];
    semlB = &shm->semaphoresB[i-1];
    while (1) {
        if (i != 0)
            P(semA);
        if (i != N - 1)
            P(semA);

        if (shm->flags[STOP]) {
            if (i != 0)
                V(semlB);
            if (i != N - 1)
                V(semrB);
            return;
        }

        if (table[idxl] > table[idxr]) {
            swap(&table[idxl], &table[idxr]);
            P(shm->mutex);
            ++(shm->flags[SWAPS]);
            V(shm->mutex);
        }

        P(shm->mutex);
        if (++(shm->flags[A]) != N) {
            V(shm->mutex);
            P(shm->blockerA);
        }

        if (--(shm->flags[A]) != 0)
            V(shm->blockerA);
        else
            V(shm->mutex);

        if (i != 0)
            V(semlB);
        if (i != N - 1)
            V(semrB);
    }
}

/**
 * Process B, indexed by i, compares i*2+1 and i*2+2 value of array in shared memory
 * and swaps it if left value is higher.
 * First, the process tries to pass its semaphore
 * Then, it checks whether the flag[STOP] isn't set to be true value. If so, process
 * stops executing.
 * Next, it compares its values and if the swap was executed, increases flag[COMP].
 * After that all processes but not the last one are stopped on stopperB. The
 * last one checks how the loop went. If there was no swap performed, then it sets
 * flag[STOP] to be true and zeroes flag[SWAP]. Then, the last process B awakened
 * opens mutex.
 * @param shm -structure with pointers to the shared memory
 * @param N - N value
 * @param i - index of the process B
 */
void processB(struct shared* shm, unsigned N, unsigned i) {
    int *table;
    unsigned idxl, idxr, sizeB;
    sem_t *semB, *semlA, *semrA;

    idxl = i * 2 + 1;
    idxr = idxl + 1;
    sizeB = N - 1;
    table = shm->table;
    semB = &shm->semaphoresB[i];
    semrA = &shm->semaphoresA[i];
    semlA = &shm->semaphoresA[i + 1];
    while (1) {
        P(semB);
        P(semB);

        if (shm->flags[STOP])
            return;

        if (table[idxl] > table[idxr]) {
            swap(&table[idxl], &table[idxr]);
            P(shm->mutex);
            ++(shm->flags[SWAPS]);
            V(shm->mutex);
        }

        P(shm->mutex);
        if (++(shm->flags[B]) == sizeB) {
            if (shm->flags[SWAPS] == 0)
                shm->flags[STOP] = 1;
            shm->flags[SWAPS] = 0;
        } else {
            V(shm->mutex);
            P(shm->blockerB);
        }

        if (--(shm->flags[B]) != 0)
            V(shm->blockerB);
        else
            V(shm->mutex);

        V(semlA);
        V(semrA);
    }
}

/**
 * Main function - first reads N value from the standard output and allocates
 * unnamed shared memory and calculates its size, then initializes helping
 * structure shm, then forks N processes A and N-1 processes B, waits for them
 * to finish and lastly prints the (hopefully) sorted array and destroys
 * everything it allocated.
 */
int main() {
    unsigned N, i, sizeB, processes_number;
    void* mapped_mem;
    struct shared shm;
    int* table;
    size_t size_mem;

    mapped_mem = init_memory(&N, &size_mem);
    init_shm(&shm, N, mapped_mem);

    table = shm.table;
    sizeB = N - 1;
    processes_number = N * 2 - 1;

    for (i = 0; i < N; ++i) {
        switch (fork()) {
            case -1:
                syserr("forkA");
                break;
            case 0:
                processA(&shm, N, i);
                munmap(mapped_mem, size_mem);
                return 0;
            default:
                break;
        }
    }

    for (i = 0; i < sizeB; ++i) {
        switch (fork()) {
            case -1:
                syserr("forkB");
                break;
            case 0:
                processB(&shm, N, i);
                munmap(mapped_mem, size_mem);
                return 0;
            default:
                break;
        }
    }

    for (i = 0; i < processes_number; ++i)
        wait(0);

    print_table(table, N);
    destruct(&shm, N);
    munmap(mapped_mem, size_mem);
    return 0;
}