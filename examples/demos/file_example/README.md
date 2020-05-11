**File Access Protocol**

A file is an operating system structure that it is used to store data.
A file structure is equiped with a set of operations for accessing
and processing the data that it stores.
Some operations are: open; read; hasNext and; close.
The order which operations an a file happen ensure a notion of correctness.
For example before reading a file you need to open it first.

We use the session typestate to describe an interaction pattern
with a file structure. The session typestate expects first to
open a file. An opened file can be read only if you perform
a succesfull hasNext check on it. If the hasNext operation
fails then the protocol expects the file to be closed.