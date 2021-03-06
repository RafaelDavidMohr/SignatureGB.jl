
# Table of Contents

1.  [Installation](#org50bba8d)
2.  [Usage](#org1968a9e)



<a id="org50bba8d"></a>

# Installation

To install this Package clone this repository to a directory of your choice:

    mkdir ~/somedir
    cd ~/somedir
    git clone https://github.com/RafaelDavidMohr/SignatureGB.jl

Then start a Julia REPL, press `]` to enter the package manager, and within `~/somedir/SignatureGB.jl` type

    (@v1.7) pkg> activate .

Now you should be able to start using this Package:

    julia> using SignatureGB

If you don't want to activate the package every time you want to use it you can do

    (@v1.7) pkg> dev ~/somedir/SignatureGB.jl/


<a id="org1968a9e"></a>

# Usage

This package exports two main functions: `f5` which computes a Gröbner basis for a polynomial ideal I using Jean Charles Faugere's F5 algorithm and `decompose` which computes the locus of highest codimension of I if given fewer generators for I than the number of variables of the underlying polynomial ring.

Both functions take as input a variable of type `Vector{spoly{n_Zp}}`, using this vector as a list of generators for I:

    using SignatureGB
    using Singular
    
    R, (x, y, z) = PolynomialRing(Fp(65521), ["x", "y", "z"])
    
    F = [x*y, x*z]
    f5(F)
    decompose(F)

Additionally, the following optional arguments might be of interest to most users:

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
<td class="org-left">The monomial order to use.</td>
<td class="org-left"><code>:GREVLEX</code></td>
<td class="org-left">Currently only grevlex is supported.</td>
</tr>


<tr>
<td class="org-left"><code>interreduction</code></td>
<td class="org-left">Whether or not to interreduce the Gröbner basis in intermediate computation steps</td>
<td class="org-left"><code>true</code></td>
<td class="org-left"><code>true</code> or <code>false</code></td>
</tr>


<tr>
<td class="org-left"><code>verbose</code></td>
<td class="org-left">Prints out computational stats. if <code>0</code>, nothing is printed. If <code>1</code>, stats are printed out at the end, for example timings and number of arithmetic operations. If <code>2</code> also print out stats about individual matrices.</td>
<td class="org-left"><code>0</code></td>
<td class="org-left"><code>0</code>, <code>1</code> or <code>2</code></td>
</tr>
</tbody>
</table>

