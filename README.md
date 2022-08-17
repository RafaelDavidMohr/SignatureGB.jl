
# Table of Contents

1.  [Installation](#orge23830b)
2.  [Usage](#orgbf97c8c)



<a id="orge23830b"></a>

# Installation

To install this Package clone this repository to a directory of your choice:

    mkdir ~/somedir
    cd ~/somedir
    git clone https://github.com/RafaelDavidMohr/SignatureGB.jl

Then start a Julia REPL, press `]` to enter the package manager, and type

    (@v1.7) pkg> add ~/somedir/SignatureGB.jl/

Now you should be able to start using this Package:

    julia> using SignatureGB


<a id="orgbf97c8c"></a>

# Usage

This package exports the function `sgb` which computes a signature Gröbner basis for an ideal using the rewrite framework by Eder and Faugére (see the correcponding [survey paper](https://arxiv.org/abs/1404.1774) for a theoretical exposition).

This function takes as input a variable of type `Vector{P}`  where `P` is a type representing polynomials inheriting from `AbstractAlgebra.MPolyElem`. For instance, both the polynomial data types from the packages `Singular.jl` and `Oscar` can be used. This vector is then used as the initial set of generators to compute a signature Gröbner basis for. Note that the behaviour of such a computation heavily depends on both the elements of this `Vector` and also the order of it. It may be advisable to sort this `Vector` by degree for example. The coefficient field of the underlying polynomial ring has to be a finite field of characteristic less than 2<sup>31</sup>.

    using SignatureGB
    using Singular
    
    R, (x, y, z) = PolynomialRing(Fp(65521), ["x", "y", "z"])
    
    F = [x*y, x*z]
    sgb(F)

Additionally, the following optional arguments might be of interest to most users. For an explanation of their mathematical meaning, see also the above mentioned [survey paper](https://arxiv.org/abs/1404.1774).

<table border="2" cellspacing="0" cellpadding="6" rules="groups" frame="hsides">


<colgroup>
<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />

<col  class="org-left" />
</colgroup>
<thead>
<tr>
<th scope="col" class="org-left">Argument</th>
<th scope="col" class="org-left">Explanation</th>
<th scope="col" class="org-left">Default</th>
<th scope="col" class="org-left">Options</th>
</tr>
</thead>

<tbody>
<tr>
<td class="org-left"><code>mon_order</code></td>
<td class="org-left">The monomial order in the GB computation</td>
<td class="org-left"><code>:GREVLEX</code></td>
<td class="org-left">Currently only grevlex supported</td>
</tr>


<tr>
<td class="org-left"><code>mod_order</code></td>
<td class="org-left">The module monomial order used for the signatures</td>
<td class="org-left"><code>:POT</code></td>
<td class="org-left"><code>:POT</code>, <code>:DPOT</code>, <code>:TOP</code>, <code>:SCHREY</code></td>
</tr>


<tr>
<td class="org-left"><code>f5c</code></td>
<td class="org-left">Whether to use the f5c optimization</td>
<td class="org-left"><code>false</code></td>
<td class="org-left"><code>true</code> or <code>false</code></td>
</tr>


<tr>
<td class="org-left"><code>all_koszul</code></td>
<td class="org-left">Whether to check the pair signatures for divisibility against all Koszul syzygy signatures. Disabling this may yield a speedup for some module orders.</td>
<td class="org-left"><code>false</code></td>
<td class="org-left"><code>true</code> or <code>false</code></td>
</tr>
</tbody>
</table>

