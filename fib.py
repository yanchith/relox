from time import time

def fib(n):
    if n == 0:
        return 0
    if n == 1:
        return 1
    return fib(n - 1) + fib(n - 2)

start = time()
f = fib(30)
end = time()

print("computed fib(30) in", end - start, seconds)

