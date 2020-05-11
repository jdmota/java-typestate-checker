This usecase intends to demonstrate how patterns of
computation that consist of a loop with sequential
dependency, i.e.~each iteration is dependent on the
previous iteration, can be expressed as a set of 
concurrent computations. The interaction between 
parallel components can be expressed using session types.

Expressing the algorithm in this way can:

i) exploit any parallelism that may exist between
sequentially dependent iterations of an algorithm; and

ii) use session types to show that the interaction
patterns of such transformations can be expressed in
a structure and descriptive way, that follows all the
properties proposed by session types. 


The protocol for Fibonacci dictates that role A decides whether to iterate over a computation
state that sends a message to role B to continue computation or send a message to role B
to end the protocol.
In the former case A sends its Fibonacci number to B, B adds
the received number to its Fibonacci number to 
compute the next Fibonacci number and sends the result back to A.
Role A then decides whether to continue computation or stop. The decision
is based on the number of iterations done, so to compute the desired Fibonacci number.
Note that each computation performed in either role A or role B, computes a
Fibonacci number.

NodeA.java implements role A and NodeB role B.