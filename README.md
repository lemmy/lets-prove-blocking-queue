# Let's prove a blocking queue deadlock-free

This is a repository of provably deadlock-free blocking queue.

This challenge was inspired by [lets-prove-leftpad](https://github.com/hwayne/lets-prove-leftpad) (from which this README and the contribution guide have been adopted).  However, while lets-prove-leftpad is about a sequential algorithm, this challenge is about a concurrent one.

Related is also Dan Ricketts' [Teaching Concurrency](https://github.com/dricketts/teaching-concurrency).

## What is "provably-correct"?

**Provably correct** is a guarantee that an algorithm satisfies given correctness properties, say deadlock freedom. You do this by providing a **proof** that a computer can check. If the proof is wrong, the computer will tell you that your algorithm is incorrect (wrt correctness properties). Or as Donald Knuth puts it: "[Beware of bugs in the above code; I have only proved it correct, not tried it.](https://www-cs-faculty.stanford.edu/~knuth/faq.html)" 

Compare to something like testing: even if you run your test for days and days, you still don't know _for sure_ that keeping it running for another minute won't reveal a deadlock. With a proof, though, you know your algorithm will be deadlock-free after a computer has verified the proof. Proving correctness is really, really powerful. It's also [time consuming](https://xavierleroy.org/talks/IHP-2014.pdf) and often not worth the effort.

This is a sampler of all the different tools we can use to prove algorithms and (implementations) correct, standardized by all being proofs for a simple concurrent data-structure most likely every programmer has encountered in her career.

## What is a "blocking queue"?

A [queue](https://en.wikipedia.org/wiki/Queue_(abstract_data_type)) that blocks until the queue becomes non-empty when consumers retrieve an element, and waits for space to become available when producers store an element. The queue has a fixed/static capacity. For simplicity, we will only consider finite and disjoint sets of producers and consumers. In other words, a producer is blocked if the queue is full; a consumer is blocked if it's empty.

The task is to prove that your blocking queue is guaranteed to never deadlock no matter the queue's capacity, the number of producers, or the number of consumers in the system. If there is space in the queue, some producer will eventually add an element to the queue. If there are elements in the queue, some consumer will eventually remove them from the queue.  More formally: Let P and C be the sets of the producer and consumer threads and let W be the set of all waiting/sleeping/blocked threads. Prove that ```(P \cup C) # W``` is a valid property of your blocking queue.

Since C is perhaps common ground for most of us, below is a listing of a blocking queue implementation:

```C
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <pthread.h>

uint32_t buff_size;
uint32_t *buffer;
uint32_t fillIndex, useIndex, count = 0;

pthread_cond_t empty, full; 
pthread_mutex_t mutex;

void put(uint32_t value) {
	buffer[fillIndex] = value;
	fillIndex = (fillIndex + 1) % buff_size;
	count++;
}

uint32_t get() {
	uint32_t tmp = buffer[useIndex];
	useIndex = (useIndex + 1) % buff_size;
	count--;
	return tmp;
}

void *producer (void * arg) {
	while(1) {
		pthread_mutex_lock(&mutex);

		while (count == buff_size)
			pthread_cond_wait(&empty, &mutex);

		put(rand() % 10);

		pthread_cond_signal(&full);
		pthread_mutex_unlock(&mutex);
	}
}

void *consumer (void * arg) {
	while(1) {
		pthread_mutex_lock(&mutex);

		while (count == 0)
			pthread_cond_wait(&full, &mutex);

		get();

		pthread_cond_signal(&empty);
		pthread_mutex_unlock(&mutex);
	} 
}

...
```

## Why are we proving deadlock freedom?

It is a great demo for different proof techniques. The idea is simple, but the algorithm (and implementations) is easy to get wrong.  The concept of concurrency is challenging for humans to get right. However, the demise of Moore's law means that algorithms have to become concurrent to keep up with growing workloads. Thus, verification pays off in this area, especially so because concurrency bugs tend to manifest in unexpected/unpredictable behavior.

A proof of deadlock-freedom is going to be small enough to be (mostly) grokkable by Formal Methods outsiders, while being complex enough to differentiate the ways we prove code correct.

## I want to contribute!

We'd love to have you! Please [read the contribution guidelines](CONTRIBUTING.md) and then submit your favorite proofs!
