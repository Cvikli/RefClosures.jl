# RefClosures.jl
Wrap `closure_expression` in a `let` block to improve efficiency.


There are cases where this is actually MUCH better then the `@closure`! due to the `Core.Box` thing when you referencing something in the outer scope. 

It solve the `Core.Box` most of the time easily. But of course you can use `Ref{T}()` many time to solve it, so there are simpler solutions sometime.
