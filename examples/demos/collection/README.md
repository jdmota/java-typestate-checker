Mungo only example of an unbounded **stack data structure** that follows a typestate specification.

The typestate specifies that a stack is initially Empty. The Empty state declares two methods: push(int) pushes an 
integer onto the stack and proceeds to the NonEmpty state; deallocate() frees any resources used by the stack and 
terminates its usage. The deallocate() method is not available in any other state, requiring a client to empty the stack
 before it is done using it. In the NonEmpty state a client can either push() an element onto the stack and remain in 
 the same state, or pop() an element from the stack and transition to Unknown. Unlike push(), pop() must leave the stack 
 in the Unknown state because the number of elements on the stack is not tracked by the protocol. From the Unknown 
 state, one can either push() and proceed to NonEmpty, or call isEmpty() to explicitly test whether the stack is empty.

**Stack** implements the StackProtocol specification.

Two stack clients are defined in StackUser and StackUser2 folders.
The first, creates a single Stack instance, stores it in a local variable s, and then passes it to various invocations 
of pushN and popAll, from which it is also returned as a result.
The second, stores a Stack as a field. To track the typestate of a field we need to know the possible sequences in which 
methods of its containing class may be called, which in turn, requires having a typestate for the containing class. 
To track the typestate of the Stack field we must provide a typestate for StackUser2. This state machine will then drive 
typestate checking for those fields of StackUser2 which have their own typestate definitions.

The two StackUsers demonstrate the basic features of mungo such as:
- local variable type inference
- protocol unfolding
- argument passing
- return values
- type field type inference

Note the recursion structures that are implemented using a combination
of a nested switch inside a labelled do while statement.