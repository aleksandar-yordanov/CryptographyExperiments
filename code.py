# Imports
import random
import math
import time
from functools import reduce
from operator import mul
from warnings import warn



'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Pre question 1: Below are utility functions defined to be used in the coursework.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
'''


large_prime =  94797311495214729293213716164658577126601400329834178992906458400053694843895119941667324463902652570638420492980522030353216754211494561802723031943185299117259199221608844683526214216111022341845135982128593049355942262431831264438267062824227856500000573155965651042867558545509678875342297706764244359971
small_prime = 23
fifteen_digit_prime = 144403552893599
six_digit_prime = 104729
thirty_digit_prime = 918481772973253507944088089607
twenty_digit_prime = 22708823198678103974314518195029102158525052496759285596453269189798311427475159776411276642277139650833937


def gcd(a, b):
    while b:
        a, b = b, a % b
    return a

def xgcd(a, b):
    s, olds = 0, 1
    r, oldr = b, a
    while r != 0:
        q = math.floor(oldr / r)
        oldr, r = r, oldr - (q * r)
        olds, s = s, olds - (q * s)
    
    if b != 0:
        bezout_t = math.floor((oldr - olds * a) / b)
    else:
        bezout_t = 0
    
    return oldr, olds, bezout_t

def SieveOfEratosthenes(n):
    sieve = [True] * n
    sieve[1] = False
    sieve[0] = False
    for i in range(2, int(math.sqrt(n)) + 1):
        if sieve[i]:
            for j in range(i * i, n, i):
                sieve[j] = False
    
    return [i for i in range(1, len(sieve)) if sieve[i]]
smallprimeset = set(SieveOfEratosthenes(100000))

def MillerRabin(n, numTrials = 8):
    #By this point we ensure that n is not in the small prime set, therefore we do not check for small primes when using miller rabin test        
    s = 0
    d = n - 1
    while d % 2 == 0:
        d >>= 1
        s += 1

    for i in range(numTrials):
        a = random.randrange(2, n)
        if pow(a, d, n) == 1:
            continue  
        
        composite = True
        for i in range(s):
            if pow(a, 2 ** i * d, n) == n - 1:
                composite = False
                break
        
        if composite:
            return False
        
        
    return True


def brent(n, c):
    # Pollard-Brent factoristion:
    # Pollard-Rho has too high of a chance of failure to be viable.

    y, r, q = random.randint(1,n-1), 1, 1
    m = 10000 # Value of 10000 found to be performant (lost source ): )

    def f(x):
        return (((x * x) % n) + c) % n

    while True:

        x = y
        for _ in range(r):
            y = f(y)
        k = 0

        while True:
            ys = y
            btlimit = min(m, r - k)
            for _ in range(btlimit):
                y = f(y)
                q = q * (abs(x - y)) % n

            g = gcd(q, n)
            k += m
            if k >= r or g > 1:
                break

        r <<= 1
        if g != 1:
            break

    if g == n:
        while True:
            ys = f(ys)
            g = gcd(abs(x - ys), n)
            if g > 1:
                break

    if g != n:
        return g
    else:
        raise Exception("Pollard Brent Factorisation Failure")

def sumDictionaries(dict1, dict2):
    return {k: dict1.get(k, 0) + dict2.get(k, 0) for k in dict1.keys() | dict2.keys()}


smallprimes = SieveOfEratosthenes(1000)
def factorint(n):
    # An optimised factorisation algorithm based on concepts in: https://stackoverflow.com/questions/4643647/fast-prime-factorization-module
    factors = {}
    for sievefactor in smallprimes:
        while n % sievefactor == 0:
            if sievefactor in factors:
                factors[sievefactor] += 1
            else:
                factors[sievefactor] = 1
            n //= sievefactor
        if sievefactor > n:
            break
    
    while n > 1:
        if n in smallprimeset:
            if n in factors:
                factors[n] += 1
            else:
                factors[n] = 1
            break
        
        if MillerRabin(n):
            if n in factors:
                factors[n] += 1
            else:
                factors[n] = 1
            break

        factor = brent(n, 1)
        ndict = factorint(factor)
        factors = sumDictionaries(factors, ndict)
        n //= factor

    return factors

'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Question 1: Diffie-Hellman Key Exchange.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
'''

def DiffieHellman(p,g,B):
    privKey = random.randint(2, p - 2)
    aliceMessage = pow(g, privKey, p)
    sharedKey = pow(B, privKey, p)

    return aliceMessage, sharedKey



'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Question 2: ElGamal:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
'''

def ElGamalEncrypt(p,g,A,x):
    secretK = random.randint(0,p-1)
    y1 = pow(g, secretK, p)
    y2 = (x * pow(A, secretK, p)) % p

    return y1, y2

def ElGamalDecrypt(p,a,y1,y2):
    s = pow(y1, a, p)
    return (y2 * pow(s,-1, p)) % p

'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Question 3: Discrete Logarithm:
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------


Current notes:

Methods compared:
Index calculus: 
    - High implementation complexity

Baby-step, Giant-step:
    - Not practical due to RAM usage.

Pollard's Rho algorith:
    - Default algorithm

Pollard's Lambda algorithm:
    - Same time complexity as rho.
    - Seems to be harder to implement.
    - Seems easier to parallelise.

https://harding.coffee/pollard-rho.pdf
https://carleton.ca/math/wp-content/uploads/Honours-Project-Dana-Nickerson.pdf
https://explained-from-first-principles.com/number-theory/#pollards-rho-algorithm
Recommended reading. 
'''


def DiscreteLogBSGS(p,g,A):
    '''
    DiscreteLogBSGS(p, g, A, n) -> returns k ∈ [0, p] such that:
    A = g^k mod p

    Return k -> The discrete logarithm satisfying the above formula 
    '''
    m = math.ceil(math.sqrt(p)) # Our 'k' value
    ajhash = {}
    for j in range(m):
        ajhash[pow(g, j, p)] = j

    modinverse = pow(g, -1, p)

    for j2 in range(m):
        val = (A * pow(modinverse, m * j2, p)) % p
        if val in ajhash:
            exp = ajhash[val]
            return exp + (m * j2)


def PollardRho(p, g, A, n):
    '''
    PollardRho(p, g, A, n) -> returns k ∈ [0, p] such that:
    A = g^k mod p

    Return k -> The discrete logarithm satisfying the above formula

    [p] = prime modulus
    [g] = generator
    [A] = target
    [n] = sub group order provided by Pohlig-Hellman


    Remarks: 
    To test outside of Pohlig-Hellman, given that g is a generator of p. Provide the group order (n) as p - 1.
    '''
    def combinedMap(x, a, b):
        # new x, a, b function.
        # Observation: For the example code on wikipedia, the order of the new_xab function seems not to match the order defined earlier in the page, 
        # When following the structure of the original defined function for f, g and h. Pollard rho fails substantially more often.
        # To clarify by order, I mean order in which path is chosen in the conditional / What we define as S0, S1 and S2.
        # new, x, a, b function source: https://en.wikipedia.org/wiki/Pollard%27s_rho_algorithm_for_logarithms
        if x % 3 == 0: # S1
            x = (x * x) % p
            a = (a * 2) % n
            b = (b * 2) % n
        elif x % 3 == 1: # S2
            x = (x * g) % p 
            a = (a + 1) % n
            b = (b)
        elif x % 3 == 2: # S0
            x = (x * A) % p
            a = (a)
            b = (b + 1) % n
        
        return x, a, b
    
    x1, a1, b1, x2, a2, b2 = 1, 0, 0, 1, 0, 0
    #it = 0 #Comment/Uncomment for debug results. 
    while True:
        #it += 1
        x1, a1, b1 = combinedMap(x1, a1, b1) # Tortoise

        x2, a2, b2 = combinedMap(x2, a2, b2) # Hare
        x2, a2, b2 = combinedMap(x2, a2, b2)
        #if it % 1000000 == 0:
        #    print(f"{it}, x1: {x1}, a1: {a1}, b1: {b1}, x2: {x2}, a2: {a2}, b2: {b2}")
        
        if x1 == x2:
            break
        
    '''
    When a conflict is found: 
    (b2 - b1)x = a1 - a2
    x = (a1 - a2) * (b2 - b1)^-1 leads to (n = gcd) solutions if the group order and (b2 - b1) are not coprime. 
    Furthermore if the gcd > 1. we cannot find find solutions to the equation as the finding the inverse of (b2 - b1) will not be invertable in the group order n.

    To find all solutions:

    1. find GCD and bezout coefficient s between a and n.
    2. find the offset between each solution as n / gcd
    3. find one possible solution as (s * (a1 - a2) // gcd) % n
    4. From 0 to GCD - 1 (denoted as m): Test s1 + (m * offset). 
    5. Return s1 + (m * offset) where that solution is the solution to the discrete logarithm.
    
    Insights for this method from explained-from-first-principles.com under DL-Algorithms -> Pollard's rho algorithm -> Solving modular equations.
    
    '''
    den = (b1 - b2) % n
    num = (a2 - a1) % n

    denGCD, b, _ = xgcd(den, n)
    
    offset = n // denGCD # Offset between each modular equation solution
    s1 = (b * num // denGCD) % n 
    for m in range(denGCD):
        k = (s1 + m * offset) % n
        if pow(g, k, p) == A:
            return k

    warn(f"Pollard Rho function has found no solution for {p, g, A}")
    return None
    

def ExhaustiveSearch(p, g, A):
    '''
    ExhaustiveSearch(p, g, A) -> returns k ∈ [0, p] such that:
    A = g^k mod p

    Return k -> The discrete logarithm satisfying the above formula

    [p] = prime modulus
    [g] = generator
    [A] = target

    Remarks: Use only for small group orders.
    '''
    k = 0
    while True:
        if pow(g, k, p) == A:
            return k
        k += 1

def solveCongruences(solutions, factors):
    '''
    solveCongruences(solutions, factors) -> Returns k such that k is a solution to the system of congruences defined with solutions[i] === factors[i]
    
    [solutions]: List = lhs -> The discrete log solutions provided by Pohlig-Hellman
    [factors]: List = rhs -> The factors for each discrete log solution provided by Pohlig-Hellman

    Solution is obtained using the chinese remainder theorem.
    '''
    def accumulate(currentAcc, i):
        y = Mproduct // factors[i]
        z = pow(y, -1, factors[i])
        return currentAcc + solutions[i] * y * z
        
    Mproduct = reduce(mul, factors, 1)
    x = reduce(accumulate, range(len(solutions)), 0)
    return x % Mproduct

def DiscreteLog(prime, g, A):
    '''
    Implementation of the Pohlig-Hellman algorithm based on the cryptography handbook and insights on https://explained-from-first-principles.com/number-theory/
    DiscreteLog(prime, g, A) -> returns k ∈ [0, p] such that:
    A = g^k mod prime

    Return k -> The discrete logarithm satisfying the above formula

    [prime] = prime modulus
    [g] = generator
    [A] = target
    '''
    n = prime - 1 # If g is a proper generator of Zp, the group order will always be p - 1
    nPrimeFactors = factorint(n)
    solutions = []
    factors = []

    for p, e in nPrimeFactors.items():
        #Implementation based on cryptography handbook 3.6.4
        xi = 0

        gamma = 1
        lPrev = 0

        gBar = pow(g, n // p, prime)

        for j in range(e):

            gamma = (gamma * pow(g, lPrev * (pow(p, (j - 1), prime)), prime)) % prime
            Abar = pow((A * pow(gamma, -1, prime)), n // (p ** (j + 1)), prime)
            
            subgroupOrder = p
            #This adaptation is sourced from https://explained-from-first-principles.com/number-theory/. PollardRho has a significant chance of failing below subgroup orders of 100. Therefore we use exhaustive search below that.
            if subgroupOrder < 100:
                lj = ExhaustiveSearch(prime, gBar, Abar)
            else:
                lj = PollardRho(prime, gBar, Abar, p)
                if lj == None:
                    raise Exception(f"Exception thrown due to pollard rho failure, Pollard Rho parameters: {prime, gBar, Abar, p}")
                    
            
            lPrev = lj
            
            xi += lj * (p ** j)
        
        solutions.append(xi)
        factors.append(p ** e)

    return solveCongruences(solutions, factors)

'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Question 3: Attacking Discrete Logarithm-Based Cryptosystems
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
'''

def DiffieHellmanCrack(p, g, A, B):
    '''
    
    Diffie-Hellman cracking method:
    You can obtain the shared key with either bob, or alices message.
    For this function we will go with bobs.

    1. First calculate alice's secret key using DiscreteLog()

    2. Calculate the shared secret with bobs message.
    
    '''
    aliceSecret = DiscreteLog(p, g, A)
    sharedKey = pow(B, aliceSecret, p)

    return sharedKey


def ElGamalCrack(p, g, A, y1, y2):
    '''
    
    ElGamal cracking method:
    1. find the secret random number k with equation 1. y1 = g^k mod p
    using DiscreteLog()

    2. Calculate the multiplicative inverse of A^k mod p.

    3. Multiply y2 by this value mod p to isolate x in the y2 equation.
    
    '''
    secretRandomNumber = DiscreteLog(p, g, y1)
    AtoKinv = pow(pow(A, secretRandomNumber, p), -1, p)

    return (y2 * AtoKinv) % p

'''
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
Post Question 4: The following section contains tests for each function.
---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
'''

def DiffieHellmenTest():
    p = 23
    g = 5   # Example generator

    def DiffieBob(p,g):
        privKey = random.randint(2,p-2)
        bobMessage = pow(g,privKey, p)
        return bobMessage, privKey

    def getBobShared(A, p, bobPriv):
        return pow(A, bobPriv, p)

    bobMsg, bobPriv = DiffieBob(p,g)
    aliceMsg, aliceSharedKey = DiffieHellman(p,g,bobMsg)
    bobSharedKey = getBobShared(aliceMsg, p, bobPriv)

    assert aliceSharedKey == bobSharedKey, "Shared keys do not match!"
    print(f"Diffie-Hellmen Test Passed, shared key successfully computed")
    
def ElGamalTest():
    p = 23
    g = 5

    def ElGamalKeyGeneration(p,g):
        privKey = random.randint(0, p-1)
        A = pow(g, privKey, p)
        return privKey, (p,g,A)

    privKey, pubKey = ElGamalKeyGeneration(p,g)
    orgMsg = 2

    y1, y2 = ElGamalEncrypt(p,g, pubKey[2], orgMsg)
    decryptedMsg = ElGamalDecrypt(p, privKey, y1, y2)
    assert decryptedMsg == orgMsg, f"Decrypted message does not match original message, Original: {orgMsg}, Decrypted: {decryptedMsg}"
    print(f"ElGamal Test Passed, Decrypted message matches: {decryptedMsg}")

def DiscreteLogTest():
    print("\nTesting correctness:")
    val = DiscreteLog(251, 71, 210)
    assert val == 197, f"Known value of 197 not found. Returned value: {val}"
    print("Discrete-Log test passed for known value of 197")
    val = DiscreteLog(1019, 2, 5)
    assert val == 10, f"Known value of 10 not found. Returned value: {val}"
    print("Discrete-Log test passed for known value of 10")
    val = DiscreteLog(59, 2, 19)
    assert val == 38, f"Known value of 38 not found. Returned value: {val}"
    print("Discrete-Log test passed for known value of 17")
    val = DiscreteLog(7000000000005000000000007, 3853985888521169485052688, 4343283804164702825621153)
    assert val == 2515895310534621204687847, f"Known value of 2515895310534621204687847 not found. Returned val: {val}"
    print("Discrete-Log test passed for known value of 2515895310534621204687847")
    print("Testing performance:")
    st = time.time()
    val = DiscreteLog(33452526613163807108170062053440751665152000000001, 8169581233628829054721498040046786736978381397990, 23569594793091565261978208222656340710382887313786)
    print(f"Performance for smooth 50 digit prime (33452526613163807108170062053440751665152000000001): {time.time() - st}")
    #st = time.time()
    #val = DiscreteLog(100003100019100043100057100069, 21866421066472035072459895860, 99710052079675826557652379052)
    #print(f"Performance for non-smooth 30 digit prime (100003100019100043100057100069): {time.time() - st}\n")

def DiffieHellmenCrackTest():
    p = six_digit_prime
    g = 5

    def DiffieBob(p,g):
        privKey = random.randint(2,p-2)
        bobMessage = pow(g,privKey, p)
        return bobMessage, privKey

    def getBobShared(A, p, bobPriv):
        return pow(A, bobPriv, p)

    bobMsg, bobPriv = DiffieBob(p,g)
    aliceMsg, aliceSharedKey = DiffieHellman(p,g,bobMsg)
    bobSharedKey = getBobShared(aliceMsg, p, bobPriv)

    sharedKey = DiffieHellmanCrack(p, g, aliceMsg, bobMsg)
    assert sharedKey == aliceSharedKey == bobSharedKey, f"Cracked shared key does not match original shared key, {p, g, aliceMsg}"
    print("Diffie-Hellmen crack test passed, cracked key matches shared key")


def ElGamalCrackTest():
    start = time.time()
    p = twenty_digit_prime
    g = 5

    def ElGamalKeyGeneration(p,g):
        privKey = random.randint(0, p-1)
        A = pow(g, privKey, p)
        return privKey, (p,g,A)

    privKey, pubKey = ElGamalKeyGeneration(p,g)
    orgMsg = 2

    y1, y2 = ElGamalEncrypt(p,g, pubKey[2], orgMsg)
    decryptedMsg = ElGamalDecrypt(p, privKey, y1, y2)

    crackedMsg = ElGamalCrack(p,g,pubKey[2], y1, y2)
    assert crackedMsg == decryptedMsg, f"Cracked message does not match decrypted message, Cracked: {crackedMsg}, Decrypted: {decryptedMsg}"
    print("ElGamal crack test passed, cracked message matches decrypted message")
    print(f"Time to crack smooth 107 digit prime: {time.time() - start}\n")

def RunTests():
    DiffieHellmenTest()
    ElGamalTest()
    DiscreteLogTest()
    DiffieHellmenCrackTest()
    ElGamalCrackTest()
    print("All tests passed.")

if __name__ == "__main__":
    RunTests()
