## Comparison between static and dynamic arbiter

When passing the following input to a static and a dynamic arbiter:

```
vec(100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10, 100, 10)
```

The static arbiter is twice as slow as the dynamic arbiter, assuming this list represents the number of cycles the
compute unit will take to output the result.

```
make test-static && make test-dynamic
./testbench-static
Finished: <V 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a  >
Cycles: 1023
./testbench-dynamic
Finished: <V 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a 'h00000064 'h0000000a  >
Cycles: 575
```
