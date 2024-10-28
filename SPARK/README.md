# SPARK submission

## About SPARK

SPARK is a subset of Ada which is amenable to formal verification. The
`gnatprove` tool allows users to prove SPARK programs.

## The implementation

This implementation uses Ada protected types which provide synchronization for
shared data. In particular, the two "entries" Enqueue and Dequeue can't be
entered in a concurrent way. Those two entries also have guards, so that the
entry can only be entered when the condition is true (otherwise it blocks).

The Ada standard defines a so-called profile (set of restrictions) called
Jorvik. One of these restrictions is that the program use a specific priority
protocol. If this priority protocol is respected, [the program is
deadlock-free](https://blog.adacore.com/spark-2014-rationale-support-for-ravenscar).
SPARK checks that this is the case for the example program.

The example program doesn't contain any tasks that would use the queue. If it
did, SPARK would also verify that the tasks only communicate via the
language-provided features such as protected types, and rendez-vous calls, and
not via e.g. unprotected global variables.

SPARK also checks that the program is free of runtime errors. This property
requires a predicate on the data, mainly stating that the `Head` and `Tail`
variables are always in the range of the buffer. One can't directly attach a
predicate to a protected type, therefore the submission uses a separate record
type which permits the definition of a predicate.


## Pointers

[SPARK repository](https://github.com/AdaCore/spark2014)
[SPARK website](https://www.adacore.com/about-spark)
[Learning SPARK](https://learn.adacore.com/courses/intro-to-spark/index.html)
