--		Copyright 1993-1999 by Daniel R. Grayson

document { pdim,
     Headline => "calculate the projective dimension",
     TT "pdim M", " -- calculate the projective dimension of a module ", TT "M", ".",
     PARA,
     "For now, the method is to measure the length of a projective resolution."
     }

document { (symbol /, Module, Module),
     Headline => "quotient module",
     TT "M/N", " -- computes the quotient module ", TT "M/N", ".",
     PARA,
     "The modules should be submodules of the same module."
     }

document { (symbol /, Module, Ideal),
     Headline => "quotient module by an ideal",
     TT "M/I", " -- computes the quotient module ", TT "M/IM", ",
     where ", TT "M", " is a module and ", TT "I", " is an ideal.",
     PARA,
     "The module and ideal should belong to the same ring."
     }

document { (symbol /, Ideal, Ideal),
     Headline => "quotient module",
     TT "I/J", " -- produces the quotient module ", TT "(I+J)/J", ", where
     ", TT "I", " and ", TT "J", " are ideals in a ring.",
     PARA,
     SEEALSO "Module"
     }

document { symbol ann,
     Headline => "the annihilator ideal",
     TT "ann", " -- a synonym for ", TO "annihilator", "."
     }

document { symbol annihilator,
     Headline => "the annihilator ideal",
     TT "annihilator M", " -- produce the annihilator ideal of a 
     module, ideal, ring element, or coherent sheaf.",
     PARA,
     "For an abbreviation, use ", TO "ann", "."
     }

document { (annihilator, Module),
     Synopsis => {
	  "I = annihilator M",
	  "M" => "a module, or an ideal or ring element",
	  "I" => { "The annihilator, ", TT "ann", "(M) = { f in R | fM = 0 }",
	       " where ", TT "R", " is the ring of ", TT "M", "."}
	  },
     TT "ann", " is a synonym for ", TT "annihilator", ".",
     EXAMPLE {
	  "R = QQ[a..d];",
	  "J = monomialCurveIdeal(R,{1,3,4})",
	  "M = Ext^2(R^1/J, R)",
	  "annihilator M"
	  },
     "For another example, we compute the annihilator of an element
     in a quotient ring",
     EXAMPLE {
	  "A = R/(a*b,a*c,a*d)",
	  "ann(a)"
	  },
     "Macaulay 2 uses two algorithms to compute annihilators.  The default
     version is to compute the annihilator of each generator of the module ",
     TT "M", " and to intersect these two by two.  Each annihilator is
     done using a submodule quotient.",
     SEEALSO {(symbol :, Module, Module), (quotient, Module, Module)}
     }

document { (symbol _,Module,ZZ),
     Headline => "get a generator",
     TT "M_i", " -- get the ", TT "i", "-th generator of a module ", TT "M", "",
     PARA,
     EXAMPLE "(ZZ^5)_2"
     }

document { (symbol ^,Module,Array),
     Headline => "projection onto some factors of a direct sum module",
     TT "M^[i,j,k]", " -- projection onto some factors of a direct sum module.",
     PARA,
     "The module ", TT "M", " should be a direct sum, and the result is the matrix
     obtained by projection onto the sum of the components numbered
     ", TT "i, j, k", ".  Free modules are regarded as direct sums.",
     PARA,
     EXAMPLE {
	  "M = ZZ^2 ++ ZZ^3",
      	  "M^[0]",
      	  "M^[1]",
      	  "M^[1,0]",
	  },
     SEEALSO {(symbol ^,Matrix,Array), (symbol _,Module,Array),(symbol ^,Module,List)}
     }

document { (symbol _,Module,Array),
     Headline => "get inclusion map into direct sum",
     TT "M_[i,j,k]", " -- get inclusion map of blocks from a module ", TT "M", ".",
     PARA,
     "The module ", TT "M", " should be a direct sum, and the result is the matrix
     obtained by inclusion from the sum of the components numbered
     ", TT "i, j, k", ".  Free modules are regarded as direct sums.",
     PARA,
     EXAMPLE {
	  "M = ZZ^2 ++ ZZ^3",
      	  "M_[0]",
      	  "M_[1]",
      	  "M_[1,0]",
	  },
     SEEALSO {submatrix, (symbol _,Matrix,Array), (symbol ^,Module,Array),(symbol _,Module,List)}
     }
document { (symbol ^, Module, List),
     Headline => "projection map from a free module",
     TT "M^{i,j,k,...}", " -- provides the projection map from a free module
     ", TT "M", " to the free module corresponding to the basis vectors whose
     index numbers are listed.",
     PARA,
     EXAMPLE "(ZZ^5)^{2,3}",
     SEEALSO {"_", Module, List}
     }

document { (symbol _, Module, List),
     Headline => "map from free module to some generators",
     TT "M_{i,j,k,...}", " -- provides a map from a free module to the module
     ", TT "M", " which sends the basis vectors to the generators of ", TT "M", "
     whose index numbers are listed.",
     PARA,
     EXAMPLE "(ZZ^5)^{2,3}",
     SEEALSO {"^", Module, List}
     }

document { (symbol _, Ideal, List),
     Headline => "map from free module to some generators",
     Synopsis => {
	  "f = I_{i,j,k,...}",
	  "I" => null,
	  "{i,j,k,...}" => "a list of integers",
	  "f" => { "a map from a free module to the module ", TT "module I", "
	       which sends the basis vectors to the generators of ", TT "I", "
     	       whose index numbers are listed."
	       }
	  },
     EXAMPLE {
	  "R = QQ[x,y,z]",
	  "I = ideal vars R",
	  "f = I_{0,2}",
	  "image f"
	  },
     SEEALSO { (module, Ideal) }
     }

document { (basis,List,Module),
     Headline => "basis of the part of a module of a certain degree",
     Synopsis => {
	  "f = basis(i,M)",
	  "i" => "the degree of the desired part of the module",
	  "M" => "a module",
	  "f" => {
	       "a map from a free module to ", TT "M", " which sends the
	       basis elements to a basis, over the ground field, of the
	       degree ", TT "i", " part of ", TT "M", "."
	       }
	  },
     "The degree ", TT "i", " is a multi-degree, represented as a list of 
     integers.  If the number of degrees is just 1, then ", TT "i", " may
     be provided as an integer.",
     SEEALSO {
	  (basis,Module),
	  "bases of parts of modules"
	  }
     }

document { (basis,Module),
     Headline => "basis of a module",
     Synopsis => {
	  "f = basis M",
	  "M" => "a module",
	  "f" => {
	       "a map from a free module to ", TT "M", " which sends the
	       basis elements to a basis, over the ground field, of ", TT "M", "."
	       }
	  },
     SEEALSO {
	  (basis,List,Module),
	  "bases of parts of modules"
	  }
     }

document { (basis,Ring),
     Headline => "basis of a ring",
     Synopsis => {
	  "f = basis R",
	  "R" => "a ring",
	  "f" => {
	       "a map from a free module to ", TT "R", " which sends the
	       basis elements to a basis, over the ground field, of ", TT "R", "."
	       }
	  },
     EXAMPLE {
	  "R = QQ[x,y]/(x^3,y^2);",
	  "basis R"
	  }
     }

document { truncate,
     Headline => "truncate the module at a specified degree",
     TT "truncate", " (i,M) -- yields the submodule of M consisting of all 
     elements of degrees >= i.  If i is a multi-degree, then this yields the
     submodule generated by all elements of degree exactly i, together with
     all generators which have a higher primary degree than that of i.",
     PARA,
     "The degree i may be a multi-degree, represented as a list of integers.
     The ring of M should be a (quotient of a) polynomial ring, 
     where the coefficient ring, k, is a field.",
     PARA,
     CAVEAT {
	  "If the degrees of the variables are not all one, then there is
     	  currently a bug in the routine: some generators of higher degree
	  than ", TT "i", " may be duplicated in the generator list."
	  },
     PARA,
     EXAMPLE {
	  "R = ZZ/101[a..c];",
      	  "truncate(2,R^1)",
      	  "truncate(2, ideal(a,b,c^3)/ideal(a^2,b^2,c^4))",
	  },
     EXAMPLE {
      	  "S = ZZ/101[x,y,z,Degrees=>{{1,3},{1,4},{1,-1}}];",
      	  "truncate({7,24}, S^1 ++ S^{{-8,-20}})"
	  },
     }
-----------------------------------------------------------------------------

TEST "
R=ZZ/101[a..f]
assert( degrees( R^{1} ++ R^{2} ) == {{-1}, {-2}} )
assert( degrees (R^{1,2} ** R^{3,5}) == {{-4}, {-6}, {-5}, {-7}} )
assert( numgens R^6 == 6 )
assert( rank R^6 == 6 )
f = vars R
M = cokernel (transpose f * f)
assert ( rank M == 5 )
assert ( rank kernel f == 5 )
assert ( rank cokernel f == 0 )
assert(R^{0,0} == R^2)
assert(R^{0,0} != R^{0,1})
"
document { GroebnerBasis,
     Headline => "the class of all Groebner bases",
     "A Groebner basis in Macaulay 2 consists of a Groebner basis
     computation, and several associated matrices. Normally you don't
     need to refer to these objects directly, as many operations on
     matrices and modules create them, and refer to them.  For more
     information, see ", TO "Groebner bases and related computations", " or
     ", TO "computing Groebner bases", "."
     }

document { (summary, GroebnerBasis),
     Headline => "display some statistics about the computation"
     }

document { (generators, GroebnerBasis),
     Headline => "the Groebner basis matrix",
     TT "generators g", " -- returns a matrix whose columns are the
     generators of the Groebner basis."
     }

document { (mingens, GroebnerBasis),
     Headline => "a matrix whose columns are minimal generators of the submodule",
     }

document { returnCode,
     TT "returnCode", " --  a key for a ", TO "GroebnerBasis", " under which is
     stored the return code from the engine for the computation."
     }

document { symbol gbTrace,
     Headline => "provide tracing output during various computations in the 	 engine.",
     TT "gbTrace = n", " -- set the tracing level for the ", TO "engine", " to
     level ", TT "n", ".  Meaningful values for the user ", TT "n", " are
     0, 1, 2, and 3.",
     PARA,
     "The notations used in tracing are :",
     MENU {
	  "g       - a generator reduced to something nonzero and has been added to the basis.",
	  "m       - an S-pair reduced to something nonzero and has been added to the basis.",
	  "z       - an S-pair reduced to zero, and a syzygy has been recorded.",
	  "u       - an S-pair reduced to zero, but the syzygy need not be recorded.",
	  "o       - an S-pair or generator reduced to zero, but no new syzygy occurred.",
	  "r       - an S-pair has been removed.",
	  "{2}     - beginning to reduce the S-pairs of multi-degree {2}.",
	  "(7)     - 7 more S-pairs among basis elements need to be reduced.",
	  "(8,9)   - there are 8 S-pairs to do in this degree, and 9 more in higher degrees.",
	  ".       - a minor has been computed, or something has happened while computing a resolution.",
	  },
     PARA,
     "The value returned is the old tracing level."
     }
     
document { gb,
     Headline => "compute a Groebner basis",
     TT "gb f", " -- compute the Groebner basis for the image of a ", TO "Matrix", " ", TT "f", ".",
     PARA,
     "If the computation is interrupted, then the partially completed
     Groebner basis is available as ", TT "f#{t,i}", ", where ", TT "t", " is true or
     false depending on whether syzygies or the change of basis matrix are 
     to be computed, and ", TT "i", " is the number of rows of the syzygy matrix to 
     be retained.  The computation can be continued by repeating the 
     ", TT "gb", " command with the same options."
     }

document { StopBeforeComputation,
     Headline => "initialize but do not begin the computation",
     TT "StopBeforeComputation", " -- an option used certain functions to cause
     the computation to be initialized but not begun."
     }

document { gb => StopBeforeComputation,
     Headline => "whether to stop the computation immediately",
     TT "StopBeforeComputation => true", " -- an optional argument used with ", TO "gb", ".",
     PARA,
     "Tells whether not to start the computation, with the default value
     being ", TT "false", ".  This can be useful when you want to obtain
     the partially computed Groebner basis contained in an interrupted
     computation."
     }

document { DegreeLimit,
     Headline => "compute up to a certain degree",
     TT "DegreeLimit => n", " -- keyword for an optional argument used with
     various functions which specifies that the computation should halt after dealing 
     with degree n."
     }

document { gb => DegreeLimit, 
     TT "DegreeLimit => n", " -- keyword for an optional argument used with
     ", TO "gb", " which specifies that the computation should halt after 
     dealing S-polynomials up to degree ", TT "n", ".",
     PARA,
     "This option is relevant only for homogeneous matrices.",
     PARA,
     "For an example, see ", TO "computing Groebner bases", "."
     }

document { BasisElementLimit, 
     Headline => "stop when this number of basis elements is obtained",
     TT "BasisElementLimit", " -- keyword for an optional argument used with
     ", TO "gb", ", ", TO "pushForward", ", ", TO "pushForward1", ", 
     and ", TO "syz", ", which can be used to specify that the computation should
     stop after a certain number of Groebner basis elements have been discovered.",
     SEEALSO "computing Groebner bases"
     }

document { SyzygyLimit,
     Headline => "stop when this number of syzygies is obtained",
     TT "SyzygyLimit", " -- keyword for an optional argument which specifies
     that the computation should stop after a certain number of syzygies 
     have computed.",
     }

document { gb => SyzygyLimit, 
     Headline => "stop when this number of syzygies is obtained",
     TT "SyzygyLimit", " -- keyword for an optional argument used with
     ", TO "gb", " which specifies that the computation should stop
     after a certain number of syzygies have computed.",
     PARA,
     "This option is relevant only if ", TT "Syzygies => true", " has
     been specified.",
     PARA,
     EXAMPLE {
	  "R = ZZ/101[x,y,z,w]",
      	  "I = ideal(x*y-z^2,y^2-w^2,w^4)",
      	  "gb(I,SyzygyLimit => 1, Syzygies => true)",
      	  "syz oo",
      	  "gb(I,SyzygyLimit => 2, Syzygies => true)",
      	  "syz oo",
      	  "gb(I,SyzygyLimit => infinity, Syzygies => true)",
      	  "syz oo"
	  },
     }

document { PairLimit,
     Headline => "stop when this number of pairs is handled",
     TT "PairLimit", " -- keyword for an optional argument used with
     certain functions which specifies that the
     computation should be stopped after a certain number of S-pairs
     have been reduced."
     }

document { gb => PairLimit, 
     Headline => "stop when this number of pairs is handled",
     TT "PairLimit", " -- keyword for an optional argument used with
     ", TO "gb", " which specifies that the
     computation should be stopped after a certain number of S-pairs
     have been reduced.",
     EXAMPLE {
	  "R = QQ[x,y,z,w]",
      	  "I = ideal(x*y-z,y^2-w-1,w^4-3)",
      	  "gb(I, PairLimit => 1)",
      	  "gb(I, PairLimit => 2)",
      	  "gb(I, PairLimit => 3)"
	  }
     }

document { CodimensionLimit,
     Headline => "stop when this codimension is reached",
     TT "CodimensionLimit => n", " -- keyword for an optional argument used with
     certain functions which specifies that the computation should stop when
     the codimension of the zero set of the ideal (or submodule) generated
     by the leading terms of the Groebner basis elements found so far reaches 
     a certain limit.",
     PARA,
     "This option has not been implemented yet.",
     PARA,
     "Eventually the codimension of the ideal of leading terms is the
     codimension of the original ideal.",
     MENU {
	  TO (gb => CodimensionLimit),
	  TO (syz => CodimensionLimit),
	  }
     }

document { gb => CodimensionLimit, 
     Headline => "stop when this codimension is reached",
     TT "CodimensionLimit => n", " -- keyword for an optional argument used with
     ", TO "gb", " which specifies that the computation should stop when
     the codimension of the zero set of the ideal (or submodule) generated
     by the leading terms of the Groebner basis elements found so far reaches 
     a certain limit.",
     PARA,
     "This option has not been implemented yet.",
     PARA,
     "Eventually the codimension of the ideal of leading terms is the
     codimension of the original ideal."
     }

document { StopWithMinimalGenerators,
     Headline => "stop when minimal generators have been determined",
     TT "StopWithMinimalGenerators", " -- an option used with certain
     functions to specify that the computation should stop as soon as a
     complete list of minimal generators for the submodule or ideal has been
     determined.",
     PARA,
     MENU {
	  TO (gb => StopWithMinimalGenerators),
	  TO (pushForward => StopWithMinimalGenerators),
	  TO (pushForward1 => StopWithMinimalGenerators),
	  TO (syz => StopWithMinimalGenerators),
	  }
     }

document { gb => StopWithMinimalGenerators, 
     Headline => "stop when minimal generators have been determined",
     TT "StopWithMinimalGenerators", " -- keyword for an optional argument used 
     with ", TO "gb", ", which, if the value provided is ", TT "true", "
     indicates that the computation should stop as
     soon as a complete list of minimal generators for the submodule
     or ideal has been determined, even if the entire Groebner basis
     has not yet been determined.",
     PARA,
     "Currently this option is implemented by stopping the computation
     as soon as the S-polynomials and generators of the same 
     degree as the generator of highest degree have been processed.",
     PARA,
     "This option is for internal use only.  Use ", TO "mingens", "
     instead."
     }

document { Strategy,
     Headline => "specify a computational strategy",
     TT "Strategy => v", " -- an optional argument used with various routines 
     to suggest a strategy for efficient computation."
     }

document { gb => Strategy, 
     Headline => "specify the strategy used to compute Groebner bases",
     TT "gb(f,Strategy => v)", " -- an option for ", TO "gb", " which can
     be used to specify the strategy to be used in the computation.",
     PARA,
     "The strategy option value ", TT "v", " should be one of the following.",
     SHIELD MENU {
	  TO "Primary",
     	  TO "Homogeneous",
	  TO "Inhomogeneous",
	  TO "LongPolynomial",
	  TO "Sort"
	  }
     }

document { Sort,
     TT "Sort", " -- a strategy used with the keyword ", TO "Strategy", ".",
     PARA,
     "Indicates that the Groebner basis should be sorted by lead term; usually
     this is a bad idea.  Normally the basis is sorted only by degree. The
     running time can change either for the good or bad."
     }

document { Primary,
     TT "Primary", " -- a strategy used with the keyword ", TO "Strategy", ".",
     PARA,
     "This is a new Groebner basis algorithm, that works in the homogeneous and
     inhomogeneous cases, and is often faster than the default algorithms.  This 
     feature is currently under development."
     }

document { Homogeneous,
     TT "Homogeneous", " -- a strategy used with the keyword ", TO "Strategy", ".",
     PARA,
     "This is an alternate Groebner basis algorithm which can be used if the submodule
     is homogeneous, and the ring is a (quotient of) a polynomial ring over a field."
     }

document { Inhomogeneous,
     TT "Inhomogeneous", " -- a strategy used with the keyword ", TO "Strategy", ".",
     PARA,
     "This is the default Groebner basis algorithm used if the submodule is
     inhomogeneous, and the ring is a (quotient of) a polynomial ring over a field."
     }

document { LongPolynomial,
     TT "LongPolynomial", " -- a strategy used with the keyword ", TO "Strategy", ".",
     PARA,
     "Indicates that during computation of a Groebner basis, the reduction
     routine will be replaced by one which will handle long polynomials more
     efficiently using \"geobuckets\", which accomodate the terms in buckets
     of geometrically increasing length.  This method was first used
     successfully by Thomas Yan, graduate student in CS at Cornell."
     }

document { Syzygies, 
     Headline => "whether to collect syzygies",
     TT "Syzygies", " -- keyword for an optional argument used with
     ", TO "gb", " which indicates whether the syzygies should be
     computed.",
     PARA,
     "It's also an option for ", TO "syz", ", but ", TO "syz", " overrides 
     any value provided by the user with the value ", TT "true", "."
     }

document { ChangeMatrix,
     Headline => "whether to produce the change of basis matrix",
     TT "ChangeMatrix", " -- a keyword for optional arguments to certain functions
     which concern a change of basis matrix."
     }

document { gb => ChangeMatrix, 
     Headline => "whether to produce the change of basis matrix",
     TT "ChangeMatrix => true", " -- an optional argument for ", TO "gb", " which
     specifies whether to compute the change of basis matrix from the basis to
     the original generators.",
     PARA,
     "Intended for internal use only."
     }
     
document { SyzygyRows, 
     Headline => "the number rows of the syzygy matrix to collect",
     TT "SyzygyRows", " -- keyword for an optional argument used with
     ", TO "gb", " and ", TO "syz", ", which specifies how many rows of 
     the syzygy matrix to retain.",
     PARA,
     "This option is for internal use only."
     }

document { getChangeMatrix,
     Headline => "get the change of basis matrix",
     TT "getChangeMatrix G", " -- for a Groebner basis G, return the change of
     basis matrix from the Groebner basis to another generating set, 
     usually a minimal, or original, generating set.",
     PARA,
     "The option ", TO "ChangeMatrix", " can be used with ", TO "gb", " 
     to enable the computation of the change of basis matrix."
     }

document { forceGB,
     Headline => "declare that the columns of a matrix are a Groebner basis",
     TT "forceGB f", " -- declares that the columns of the matrix ", TT "f", "
     constitute a Groebner basis, and returns a Groebner basis object
     encapsulating that assertion.",
     PARA,
     "We should probably rename this function or incorporate it into
     ", TO "gb", " somehow."
     }

document { forceGB => ChangeMatrix,
     Headline => "set the change of basis matrix",
     TT "ChangeMatrix => p", " -- an optional argument for ", TO "forceGB", " which
     which specifies that the change of basis matrix is ", TT "p", "."
     }

document { MinimalMatrix,
     Headline => "set the matrix of minimal generators",
     TT "MinimalMatrix => g", " -- an option for ", TO "forceGB", " which
     specifies that the columns of g are minimal generators for the submodule
     generated by the Groebner basis."
     }

document { SyzygyMatrix,
     Headline => "set the syzygy matrix",
     TT "SyzygyMatrix => h", " -- an option for ", TO "forceGB", " which
     specifies that the columns of h are the syzygies for the Groebner basis."
     }
    

TEST "
R = ZZ/103[a..c]
C = resolution cokernel vars R
assert(regularity C === 0)
R = ZZ/101[a .. r]
M = cokernel genericMatrix(R,a,3,6)
time C = resolution M
assert(regularity C === 2)
f = symmetricPower(2,vars R)
assert(f%a + a * (f//a) == f)
"

TEST "
S = ZZ/101[t_1 .. t_9,u_1 .. u_9]
m = matrix pack (3,toList (t_1 .. t_9))			  -- 3 by 3
n = matrix pack (3,toList (u_1 .. u_9))			  -- 3 by 3
j = flatten (m * n - n * m)
k = flatten (m * n - n * m)
G = gb j
jj = generators G
assert( numgens source jj == 26 )
T = (degreesRing S)_0
assert( poincare cokernel j == 1-8*T^2+2*T^3+31*T^4-32*T^5-25*T^6+58*T^7-32*T^8+4*T^9+T^10 )
v = apply(7, i -> numgens source generators gb(k,DegreeLimit => i) )
assert (v  === {0, 0, 8, 20, 25, 26, 26} )
"

document { mingens,
     Headline => "returns a minimal generatoring set of a graded module",
     TT "mingens M", " -- returns a minimal generating set for the module ", TT "M", ",
     represented as a matrix whose target is the ambient free module of ", TT "M", ".",
     PARA,
     SEEALSO "GroebnerBasis"
     }

TEST "
R = ZZ/101[a..d]
f = matrix{{a,b},{c,d}}
h = matrix {{1,0,0},{0,c,d}}
M = subquotient(h,f)
assert( mingens M == matrix (R, {{1},{0}}))
"
document { trim,
     Headline => "simplify the presentation",
     TT "trim M", " -- produce a module isomorphic to the module M obtained
     by replacing its generators by a minimal set of generators, and doing
     the same for the relations.",
     PARA,
     "Also works for rings and ideals.",
     PARA,
     EXAMPLE {
	  "R = ZZ/101[x]",
      	  "M = subquotient( matrix {{x,x^2,x^3}}, matrix {{x^3,x^4,x^5}})",
      	  "trim M"
	  }
     }

TEST "
R = ZZ/101[a..d]
f = matrix{{a,b},{c,d}}
h = matrix {{1,0,0},{0,c,d}}
M = subquotient(h,f)
assert( generators trim M == matrix (R, {{1},{0}}))
"

document { syz => StopWithMinimalGenerators,
     Headline => "stop when minimal generators have been determined",
     TT "StopWithMinimalGenerators => true", " -- an optional argument used 
     with ", TO "syz", " that specifies that the computation should stop as soon as a
     complete list of minimal generators for the submodule or ideal has been
     determined.",
     PARA,
     "The value provided is simply passed on to ", TO "gb", ": see 
     ", TO (gb => StopWithMinimalGenerators), " for details."
     }

document { syz => Strategy,
     Headline => "specify the strategy used to compute the Groebner basis",
     TT "syz(f,Strategy => v)", " -- an option for ", TO "syz", " which can
     be used to specify the strategy to be used in the computation.",
     PARA,
     "The value of the option is simply passed to ", TO "gb", ", so see the
     documentation there for details."
     }

document { syz => CodimensionLimit,
     Headline => "stop when this codimension is reached",
     TT "CodimensionLimit => n", " -- keyword for an optional argument used with
     ", TO "syz", " which specifies that the computation should stop when
     the codimension of the zero set of the ideal (or submodule) generated
     by the leading terms of the Groebner basis elements found so far reaches 
     a certain limit.",
     PARA,
     "This option has not been implemented yet.",
     PARA,
     "Eventually the codimension of the ideal of leading terms is the
     codimension of the original ideal.",
     }

document { syz,
     Headline => "the syzygy matrix"
     }

document { (syz, GroebnerBasis),
     Headline => "retrieve the syzygy matrix",
     Synopsis => {
	  "f = syz G",
	  "G" => {"the Groebner basis of a matrix ", TT "h"},
	  "f" => {"the matrix of syzygies among the columns of ", TT "h"}
	  },
     "Warning: the result may be zero if syzygies were not to be retained 
     during the calculation, or if the computation was not continued to a
     high enough degree.",
     }

document { (syz, Matrix),
     Headline => "compute the syzygy matrix",
     Synopsis => {
	  "f = syz h",
	  "h" => {"a matrix"},
	  "f" => {"the matrix of minimal generators for the syzygies among
	       the columns of ", TT "h"}
	  }
     }

document { syz => StopBeforeComputation,
     Headline => "whether to stop the computation immediately",
     TT "StopBeforeComputation => true", " -- an optional argument used with ", TO "gb", ".",
     PARA,
     "Tells whether not to start the computation, with the default value
     being ", TT "false", ".  This can be useful when you want to obtain
     the partially computed Groebner basis contained in an interrupted
     computation."
     }

document { syz => ChangeMatrix,
     Headline => "whether to produce the change of basis matrix",
     TT "ChangeMatrix => true", " -- an optional argument for ", TO "syz", " which
     specifies whether to compute the change of basis matrix."
     }

document { modulo,
     Headline => "find the pre-image of a map (low level version)",
     "modulo(f,g) - given homomorphisms ", TT "f", " and ", TT "g", " of free 
     modules with the same target, produces a homomorphism of free modules whose 
     target is the source of ", TT "f", ", and whose image is the pre-image (under
     ", TT "f", ") of the image of ", TT "g", ".",
     PARA,
     "If ", TT "f", " is null, then it's taken to be the identity.  If ", TT "g", " is null, it's
     taken to be zero."
     }
document { (symbol //, Matrix, Matrix),
     Headline => "factor a map through another",
     TT "f//g", " -- yields a matrix ", TT "h", " from matrices ", TT "f", " and ", TT "g", " 
     such that ", TT "f - g*h", " is the reduction of ", TT "f", " modulo a Groebner basis 
     for the image of ", TT "g", ".",
     PARA,
     "If the remainder ", TT "f - g*h", " is zero, then the quotient ", TT "f//g", "
     satisfies the equation ", TT "f = g * (f//g)", ".",
     SEEALSO {(symbol %, Matrix, Matrix)}
     } 

TEST "
R = ZZ/101[a..d]
A = image matrix {{a}}
B = image matrix {{b}}
f = map((A+B)/A, B/intersect(A,B))
assert isIsomorphism f
g = f^-1
assert( f^-1 === g )			  -- check caching of inverses
assert( f*g == 1 )
assert( g*f == 1 )
assert isWellDefined f
assert isWellDefined g
assert not isWellDefined map(R^1,cokernel matrix {{a}})
"

document { (symbol //, Matrix, RingElement),
     Headline => "factor a map through a multiplication map",
     TT "f//r", " -- yields a matrix h from a matrix f and a ring element r
     such that f - r*h is the reduction of f modulo a Groebner basis 
     for the image of r times the identity matrix.",
     SEEALSO "%"
     } 

document { (symbol %, Matrix, Matrix),
     Headline => "find the normal form modulo the image of a map",
     TT "f % g", " -- yields the reduction of the columns of the matrix
     ", TT "f", " modulo a Groebner basis of the matrix ", TT "g", "."
     }

document { (symbol %, Matrix, RingElement),
     Headline => "reduce the columns modulo of a ring element",
     TT "f % r", " -- yields the reduction of the columns of the matrix
     ", TT "f", " modulo the ring element ", TT "r", "."
     }

document { complement,
     Headline => "find the minimal generators for cokernel of a matrix (low level form)",
     TT "complement f", " -- for a matrix ", TT "f", ", return a map ", TT "g", " with the same
     target whose columns are minimal generators for the cokernel of ", TT "f", ".",
     PARA,
     "The map ", TT "f", " must be homogeneous."
     }

-----------------------------------------------------------------------------

TEST "
S = ZZ/107[vars ( 0 .. 5 ) ]

g = matrix {{a*b*c - d*e*f, a*d^2 - e^3, a*e^2 - b*c*e}}
k = syz g
assert( numgens source k === 4 )

t = (a + b + c)^4 
u = (a + b + c) * b^3
v = a * t + b * u
w = c * t - d * u
x = b * t + f * u

h = matrix {{t,u,v,w,x}}
h1 = mingens image h

so = m -> m_(sortColumns m)

assert ( so h1 == so matrix {{
	       a^4+4*a^3*b+6*a^2*b^2-3*b^4+4*a^3*c+12*a^2*b*c+12*a*b^2*c+6*a^2*c^2
	       +12*a*b*c^2+6*b^2*c^2+4*a*c^3+4*b*c^3+c^4,
	       a*b^3+b^4+b^3*c
	       }} )
"

document { index,
     Headline => "yields the numeric index of a ring variable",
    TT "index v", " -- yields the numeric index of the variable 'v' in its ring.
    Variables are indexed starting at 0, and ending at n-1, where n is the number
    of variables in the ring of 'v'.",
    PARA,
    EXAMPLE {
	 "R = ZZ/101[a..d,t]",
     	 "index a",
     	 "index t",
	 },
    "If the ring element 'v' is not a variable, an error is generated.",
    PARA,
    "The symbol ", TT "index", " is also as a key used in 
    ", TO {"GeneralOrderedMonoid", "s"}, " to store a table which is used to 
    map generator names to the position of the generator in the list of generators."
    }

TEST "
    R = ZZ/101[x_0 .. x_10]
    scan(11, i -> assert(index x_i == i))
    assert( try (index x_11;false) else true )
    R = ZZ/101[w,z,t,e]
    assert( index w == 0 )
    assert( index z == 1 )
    assert( index t == 2 )
    assert( index e == 3 )
"

document { homogenize,
     Headline => "homogenize with respect to a variable",
     TT "homogenize(m,v)", " -- homogenize the ring element, vector,
     matrix, or module ", TT "m", " using the variable ", TT "v", " in the ring of ", TT "m", ".",
     BR,
     NOINDENT,     
     TT "homogenize(m,v,w)", " -- homogenize ", TT "m", " using the variable ", TT "v", ",
     so that the result is homogeneous with respect to the given list ", TT "w", " of
     integers provided as weights for the variables.",
     PARA,
     EXAMPLE {
	  "R = ZZ/101[x,y,z,Degrees => {1,2,3}]",
      	  "f = 1 + y + z^2",
      	  "homogenize(f,x)",
      	  "homogenize(f,x,{1,0,-1})",
	  },
     PARA,
     "The weights that may be used are limited (roughly) to the range -2^30 .. 2^30.",
     PARA,
     CAVEAT {
	  "If the homogenization overflows the monomial, this is not
     	  reported as an error."
	  }
     }

TEST "
R = ZZ/101[a..d,t]
f = a^2-d^3*b-1
assert(homogenize(f,t) == a^2*t^2 - d^3*b - t^4)
assert(homogenize(f,t,{1,2,3,4,2}) == a^2*t^6 - d^3*b - t^7)
assert(homogenize(f,b,{1,1,0,-1,1}) == a^2 - d^3*b^5 - b^2)

m = map(R^{1,-1}, , {{a,b},{c,d-1}})
assert(homogenize(m,t) == map(R^{1,-1}, , {{a*t^2, b*t^2}, {c, d-t}}))
assert(homogenize(m,t,{-1,-1,-1,-1,1}) == map(R^{1,-1}, , {{a*t^2, b*t^3}, {c, d*t-1}}))

v = m_0
F = class v
assert(homogenize(v,t) == a*t^2 * F_0 + c * F_1)
assert(homogenize(v,t,{-1,-1,-1,-1,1}) == a*t^2 * F_0 + c * F_1)

-- now check to make sure that all is ok over quotient rings
R = ZZ/101[a..d]/(a^2-b^2, a*b)
use R
f = c^2 - 1 + b^2 - b
assert(homogenize(f,a) == c^2)
"

document { terms,
     Headline => "provide a list of terms of a polynomial",
     TT "terms f", " -- provide a list of terms of a polynomial.",
     PARA,
     EXAMPLE {
	  "R = QQ[x,y]",
      	  "terms (x+2*y-1)^2",
	  },
     SEEALSO "coefficients"
     }

document { Ascending,
     TT "Ascending", " -- a symbol used as a value for optional
     arguments ", TO "DegreeOrder", " and ", TO "MonomialOrder", "."
     }

document { Descending,
     Headline => "specify descending order",
     TT "Descending", " -- a symbol used as a value for optional
     arguments ", TO "DegreeOrder", " and ", TO "MonomialOrder", "."
     }

document { DegreeOrder,
     Headline => "sort primarily by degree",
     TT "DegreeOrder", " -- an optional argument for use with certain
     functions, used to specify sort order."
     }

document { (sortColumns => DegreeOrder),
     Headline => "sort primarily by degree",
     TT "DegreeOrder => x", " -- an optional argument for use with the function
     ", TO "sortColumns", ".",
     PARA,
     "The possible values for ", TT "x", " are ", TO "Ascending", ",
     ", TO "Descending", ", and ", TO "null", "."
     }

document { (sortColumns => MonomialOrder),
     Headline => "specify Ascending or Descending sort order",
     TT "MonomialOrder => x", " -- an optional argument for use with the function
     ", TO "sortColumns", ".",
     PARA,
     "The possible values for ", TT "x", " are ", TO "Ascending", " (the default value) and
     ", TO "Descending", "."
     }

document { sortColumns,
     Headline => "sort the columns of a matrix",
     TT "sortColumns f", " -- sorts the columns of a matrix, returning a list of integers
     describing the resulting permutation.",
     PARA,
     "The sort ordering used is by degree first, and then by monomial order.  Optional
     arguments may be given to specify whether the ordering is ascending, descending,
     or ignored.  The default ordering is ascending.",
     PARA,
     EXAMPLE {
	  "R = ZZ/101[a..c];",
      	  "f = matrix{{1,a,a^2,b^2,b,c,c^2,a*b,b*c,a*c}}",
      	  "s = sortColumns f",
      	  "f_s",
      	  "s = sortColumns(f,DegreeOrder => Descending)",
      	  "f_s"
	  },
     }

document { selectInSubring,
     Headline => "select columns in a subring",
     TT "selectInSubring(i,m)", " -- Form the submatrix of the matrix 'm' consisting of those
     columns which lie in the subring generated by all but the first 'i' parts of the
     monomial order.",
     PARA,
     "We say that a monomial ordering has n 'parts' if the variables are partitioned
     into n subsets in such a way that for each j, any monomial smaller than a
     monomial that involves variables only from the last j parts, also involves
     variables only from the last j parts.  Such monomial orderings include
     product orderings, lexicographic orderings, and elimination orderings.",
     PARA,
     "For example, consider the lexicographic ordering of four variables, where
     the parts are the singletons ", TT "{a}, {b}, {c}, {d}", ".",
     EXAMPLE {
	  "R = ZZ/101[a..d,MonomialOrder=>Lex]",
      	  "m = matrix{{b^2-c^2, a^2 - b^2, c*d}}",
      	  "selectInSubring(1,m)",
      	  "selectInSubring(2,m)",
      	  "selectInSubring(3,m)",
	  },
     PARA,
     CAVEAT {
	  "This routine doesn't do what one would expect for graded orders
     	  such as ", TT "GLex", ".  There, the first part of the monomial 
	  order is the degree, which is usually not zero.  This routine 
	  should detect and correct this."
     },
     SEEALSO "monomial orderings"
     }

document { divideByVariable,
     Headline => "divide all columns by a (power of a) variable",
     TT "divideByVariable(m,v)", " -- divide each column of the matrix 'm' by 
     as high a power of the variable 'v' as possible.",
     BR,NOINDENT,
     TT "divideByVariable(m,v,d)", " -- divide each column of the matrix 'm' by 
     as high a power of the variable 'v' as possible, but divide by no more than v^d.",
     PARA,
     EXAMPLE {
	  "R = ZZ/101[a..d]",
      	  "m = matrix{{a*b, a^2*c}, {a*b^2, a^4*d}}",
      	  "divideByVariable(m,a)",
      	  "divideByVariable(m,a,1)",
	  },
     CAVEAT "You can only divide by a variable, not a monomial,
     and you have little control on what power will be divided.  This routine is mostly
     used by the saturation commands as a fast internal way of dividing.",
     PARA,
     "We may eliminate this routine."
     }

document { compress,
     Headline => "remove columns which are zero",
     TT "compress m", " -- provides the matrix obtained from the matrix ", TT "m", "
     by removing the columns which are zero."
     }

document { newCoordinateSystem,
     Headline => "change variables",
     TT "newCoordinateSystem(S,m)", " -- takes a one-rowed matrix ", TT "m", " of
     independent linear forms over a ring ", TT "R", " and returns a list 
     ", TT "{f,g}", ", where ", TT "f", " is a ring map given by some linear change 
     of coordinates from ", TT "R", " to ", TT "S", " which sends the last variables 
     of ", TT"R", " to the forms in ", TT "m", ", and ", TT "g", " is the inverse 
     of ", TT "f", ".",
     PARA,
     "The ring ", TT "S", " should have the same number of variables as 
     ", TT "S", ".",
     EXAMPLE {
	  "R = ZZ/101[a..d]",
      	  "S = ZZ/101[p..s]",
      	  "newCoordinateSystem(S,matrix{{a+2*b,3*c-d}})"
	  },
     }

document { PrimitiveElement,
     Headline => "specify a primitive element",
     TT "PrimitiveElement => g", " -- an option used with ", TO "GF", ".",
     PARA,
     "The value can be a ring element providing a primitive element, or the
     symbol ", TO "FindOne", " (the default) which specifies that
     ", TO "GF", " should search for a primitive element."
     }

document { FindOne,
     Headline => "find a primitive element",
     TT "FindOne", " -- a value for the option ", TO "PrimitiveElement", "
     to ", TO "GF", " which specifies that ", TO "GF", " should search 
     for a primitive element."
     }

document { Variable,
     Headline => "specify a name for the generator of a Galois field",
     TT "Variable => x", " -- an option used with ", TO "GF", ", to specify
     a symbol to be used as a name for the generator of the Galois field."
     }

document { GaloisField, Headline => "the class of all Galois fields" }
document { GF, Headline => "make a finite field" }
document { (GF,Ring), Headline => "make a finite field from a ring",
     TT "GF R", " -- make a Galois field from a quotient ring R which happens
     to be isomorphic to a finite field.",
     EXAMPLE {
	  "k = GF(ZZ/2[t]/(t^3+t+1))",
	  "t+t^2"
	  }
     }
document { (GF,ZZ,ZZ), Headline => "make a finite field of a given prime power order",
     TT "GF(p,n)", " -- make a Galois field with ", TT "p^n", " elements, where 
     ", TT "p", " is a prime.",
     EXAMPLE {
	  "k = GF(2,3,Variable=>x)",
	  "x+x^2"
	  }
     }
document { (GF,ZZ), Headline => "make a finite field of a given order",
     TT "GF(q)", " -- make a Galois field with ", TT "q", " elements, where 
     ", TT "q", " is a power of a prime.",
     EXAMPLE {
	  "k = GF(8)",
	  "x = k_0",
	  "x+x^2"
	  }
     }

TEST "
R=ZZ/2[t]
assert isPrime (t^2+t+1)
assert (not isPrime (t^2+1))
"

document { isPrimitive, Headline => "whether an element is a primitive element of a finite field",
     TT "isPrimitive(f)", " -- Given an element ", TT "f", " in a quotient of a polynomial ring ",
     TT "R", " over a finite field ", TT "K", "which is itself a finite field,
      with the ring being finite dimensional over the field,
     determine if ", TT "f", " generates the multiplicative group of this field.",
     EXAMPLE { "R = ZZ/5[t]/(t^2+t+1);", "isPrimitive t", "isPrimitive (t-1)" }
     }

TEST "
R = ZZ/5[t]/(t^2+t+1)
assert (not isPrimitive t)
assert isPrimitive (t-1)
assert (not isPrimitive 0_R)
"

document { order,
     Headline => "a key used internally ",
     TT "order", " -- used as a key inside finite fields under which is
     stored the number of elements in the field.  Intended for internal use only",
     PARA,
     SEEALSO "GaloisField"
     }

document { isField, Headline => "whether something is a field",
     "No computation is done -- the question is whether the ring was
     explicitly constructed a field.",
     SEEALSO "toField"
     }

document { toField, Headline => "declare that a ring is a field",
     Synopsis => {
	  "toField R",
	  "R" => "a ring",
     	  null
	  },
     "Use this to declare that a ring ", TT "R", " is known to be a field.  This
     is accomplished by setting ", TT "R.isField", " to be ", TT "true", ",
     and, in case the ring is a ring handled by the engine, informing the
     engine.  Polynomial rings over rings declared to be fields support
     Groebner basis operations.",
     PARA,
     "If the engine eventually discovers that some nonzero element of ", TT "R", "
     is not a unit, an error will be signalled.  The user may then use
     ", TO "getNonUnit", " to obtain a non-invertible element of ", TT "R", ",
     or ", TO "getZeroDivisor", " to obtain a zero divisor in ", TT "R", ".
     If a ring is probably a field, it can be used as a field until a
     contradiction is found, and this may be a good way of discovering
     whether a ring is a field."
     }

document { getNonUnit, Headline => "retrieve a previously discovered non-unit",
     Synopsis => {
	  "r = getNonUnit R",
	  "R" => "a ring in which division by a non-unit has been attempted",
	  "r" => "the non-unit"
	  },
     "Warning: this function does not work yet for divisions attempted in the course
     of computing a Groebner basis or resolution.",
     SEEALSO { "toField", "getZeroDivisor" }
     }

document { getZeroDivisor, Headline => "retrieve a previously discovered zero divisor",
     Synopsis => {
	  "r = getZeroDivisor R",
	  "R" => "a ring in which a zero-divisor has been found",
	  "r" => "the zero divisor"
	  },
     SEEALSO { "toField", "getNonUnit" }
     }

document { isAffineRing, Headline => "whether something is an affine ring",
     "An affine ring is a quotient of a polynomial ring over a field."
     }

document { RingMap,
     Headline => "the class of all ring maps",
     "Common ways to make a ring map:",
     MENU {
	  TO (map,Ring,Ring),
	  TO (map,Ring,Ring,List),
	  TO (map,Ring,Ring,Matrix),
	  },
     "Common ways to get information about ring maps:",
     MENU {
	  TO (isHomogeneous, RingMap),
	  TO (isInjective, RingMap)
	  },
     "Common operations on ring maps:",
     MENU {
	  TO (symbol *, RingMap, RingMap),
	  TO (kernel, RingMap),
	  TO (coimage, RingMap)
	  },
     "Common ways to use a ring map:",
     MENU {
	  TO (symbol " ", RingMap, Matrix),
	  TO (symbol " ", RingMap, Ideal),
	  TO (symbol " ", RingMap, Module),
	  TO (symbol **, RingMap, Module)
	  },
     }

document { (symbol **, RingMap, Module),
     Synopsis => {
	  "N = f ** M",
	  "f" => { "a ring map from ", TT "R", " to ", TT "S", "." },
	  "M" => { "an ", TT "R", "-module" },
	  "N" => { "the tensor product of ", TT "M", " with ", TT "S", " over ", TT "R", "." }
	  },
     EXAMPLE {
	  "R = QQ[x,y];",
	  "S = QQ[t];",
	  "f = map(S,R,{t^2,t^3})",
	  "f ** coker vars R",
	  "f ** image vars R"
	  },
     SEEALSO { (symbol " ", RingMap, Module) }
     }

document { (symbol " ", RingMap, Module),
     Synopsis => {
	  "N = f M",
	  "f" => { "a ring map from ", TT "R", " to ", TT "S", "." },
	  "M" => { "a free ", TT "R", "-module ", TT "R^n", " or a submodule of one" },
	  "N" => { "the submodule of ", TT "S^n", " generated by the image of ", TT "M", "." }
	  },
     EXAMPLE {
	  "R = QQ[x,y];",
	  "S = QQ[t];",
	  "f = map(S,R,{t^2,t^3})",
	  "f image vars R"
	  },
     SEEALSO { (symbol " ", RingMap, Module) }
     }

document { DegreeMap,
     "A name for an optional argument used with ", TT "map", " when
     creating a ring map.",
     SEEALSO { map => DegreeMap }
     }

document { map => DegreeMap,
     "A name for an optional argument used with ", TT "map", " when
     creating a ring map, to specify a function that transforms degrees
     of elements in the source ring to degrees of elements in the
     target ring.  The function will be used later when tensoring a
     module along the ring map to determine the degrees of the
     generators in the result, and to determine whether the map is
     homogeneous.",
     EXAMPLE {
	  "R = QQ[x,y,z];",
	  "S = QQ[t,u];",
	  "f = map(S,R,{t^2,t*u,u^2},DegreeMap => i -> 2*i)",
	  "isHomogeneous f",
	  "M = R^{1,2}",
	  "f ** M"
	  },
     "The default degree map function is the identity function, but when the two
     rings have different degree lengths, a function must be explicitly
     provided that transforms the lengths of the degree vectors appropriately, 
     or else the default function which maps every degree to {0,...,0} 
     will be provided automatically."
     }

document { (map,Ring,Ring,Matrix),
     Headline => "make a ring map",
     Synopsis => {
	  "f = map(R,S,m)",
	  "R" => "the target ring",
	  "S" => "the source ring",
	  "m" => {"a 1 by n matrix over ", TT "R", ", where n is the
     	       number of variables in the polynomial ring ", TT "S", ",
	       or a matrix over the common coefficient ring of the 
	       two rings."
	       },
	  "f" => {
	       "the ring homomorphism from ", TT "S", " to ", TT "R", " which,
	       in case m is a matrix over R, sends the i-th variable
	       of ", TT "S", " to the i-th entry in ", TT "m", ",
	       or, in case ", TT "m", " is a matrix over the common coefficient ring,
	       is the linear change of coordinates corresponding to ", TT "m", "."
	       }
	  },
     EXAMPLE {
	  "R = ZZ[x,y];",
	  "S = ZZ[a,b,c];",
	  "f = map(R,S,matrix {{x^2,x*y,y^2}})",
	  "f(a+b+c^2)",
	  "g = map(R,S,matrix {{1,2,3},{4,5,6}})",
	  "g(a+b)"
	  },
     "If the coefficient ring of ", TT "S", " is itself a polynomial ring, then
     one may optionally include values to which its variables should be 
     sent: they should appear first in the matrix ", TT "m", ".",
     EXAMPLE {
	  "S = ZZ[a][b,c];",
	  "h = map(S,S,matrix {{b,c,a}})",
	  "h(a^7 + b^3 + c)",
	  "k = map(S,S,matrix {{c,b}})",
	  "k(a^7 + b^3 + c)"
	  }
     }

document { (map,Ring,Ring,List),
     Headline => "make a ring map",
     Synopsis => {
	  "f = map(R,S,m)",
	  "R" => "the target ring",
	  "S" => "the source ring",
	  "m" => {"a list of n elements of ", TT "R", ", where n is the
     	       number of variables in the polynomial ring ", TT "S", "."
	       },
	  "f" => {
	       "the ring homomorphism from ", TT "S", " to ", TT "R", " which sends the i-th variable
	       of ", TT "S", " to the i-th entry in ", TT "m", "."
	       }
	  },
     EXAMPLE {
	  "R = ZZ[x,y];",
	  "S = ZZ[a,b,c];",
	  "f = map(R,S,{x^2,x*y,y^2})",
	  "f(a+b+c^2)"
	  },
     SEEALSO {(map,Ring,Ring,Matrix)}
     }

document { substitute,
     Headline => "substitute values for variables",
     TT "substitute(f,v)", " -- substitute values for the variables in the matrix,
     module, vector, polynomial, or monomial ", TT "f", " as specified by ", TT "v", ".", 
     PARA,
     "If ", TT "f", " is a matrix over ", TT "R", ", and ", TT "v", " is a 1 by k matrix over another
     ring ", TT "S", ", then the result is obtained by substituting the entries in ", TT "v", " 
     for the variables in ", TT "R", ".",
     PARA,
     "If ", TT "f", " is a module over ", TT "R", ", then substitution amounts to substitution
     in the matrices of generators and relations defining the module.  This is
     not the same as tensor product!",
     PARA,
     "If ", TT "v", " is a ring, then the result is obtained by substituting the variables of
     ", TT "v", " for the variables of R with the same name.  The substitution extends
     to the coefficient ring of ", TT "R", ", and so on.",
     PARA,
     "If ", TT "v", " is a list of options ", TT "{a => f, b => g, ...}", " then the 
     variable ", TT "a", " is replaced by the polynomial ", TT "f", ", etc.  Warning: 
     this may lead to surprising results if the ring containing f and g doesn't have 
     the same coefficient ring as the ring containing f, because currently no checking 
     is done to see whether the substitution requested corresponds to a well-defined
     ring homomorphism.",
     EXAMPLE {
	  "R = ZZ/101[x,y,z]",
      	  "f = x+2*y+3*z",
      	  "substitute(f,{x=>x^3, y=>y^3})",
      	  "S = ZZ/101[z,y,x]",
      	  "substitute(f,S)"
	  },
     "Warning: the specified substitution is not checked to see whether
     the corresponding ring homomorphism is well-defined; this may produce
     surprising results, especially if rational coefficients are converted
     to integer coefficients.",
     PARA,
     "A convenient abbreviation for ", TO "substitute", " is ", TO "sub", "."
     }


document { modifyRing,
     Headline => "make a copy of a ring, with some features changed",
     TT "modifyRing(R,options)", " -- yields a ring similar to R, with 
     certain features changed.",
     PARA,
     "Bug: doesn't work yet."
     }

TEST "
    R = ZZ/101[a..d,Degrees=>{1,2,3,4}]
    S = modifyRing(R,Degrees=>{1,1,1,1})
    S1 = modifyRing(R,MonomialOrder=>Eliminate 2,Degrees=>{1,1,1,1})
"

document { (symbol **, Ring, Ring), Headline => "tensor product",
     "For complete documentation, see ", TO "tensor", "."
     }

document { graphIdeal,
     Headline => "the ideal of the graph of a ring map",
     TT "graphIdeal f", " -- provides the ideal of the graph of the map
     associated to the ring map f.",
     SEEALSO "graphRing"
     }

document { graphRing,
     Headline => "the ring of the graph of a ring map",
     TT "graphRing f", " -- provides the ring of the graph of the map
     associated to the ring map f.",
     SEEALSO "graphIdeal"
     }

document { symmetricAlgebra,
     Headline => "the symmetric algebra of a module",
     TT "symmetricAlgebra M", " -- produces the symmetric algebra of a
     module M.",
     PARA,
     "Bugs: uses symbols from the beginning of the alphabet as variables in
     the new ring; makes a quotient ring when it doesn't have to."
     }

document { NonLinear,
     Headline => "use the algorithm which doesn't assume that the ring map is linear",
     TT "Strategy => NonLinear", " -- an option value for the ", TO "Strategy", "
     option to ", TO "pushForward1", "."
     }

document { pushForward1 => StopBeforeComputation,
     Headline => "initialize but do not begin the computation",
     TT "StopBeforeComputation", " -- keyword for an optional argument used with
     ", TO "pushForward1", ".",
     PARA,
     "Tells whether to start the computation, with the default value
     being ", TT "true", "."
     }

document { pushForward1 => DegreeLimit,
     Headline => "compute only up to this degree",
     TT "DegreeLimit => n", " -- keyword for an optional argument used with
     ", TO "pushForward1", " which specifies that the computation should halt after dealing 
     with degree ", TT "n", ".",
     PARA,
     "This option is relevant only for homogeneous matrices.",
     PARA,
     "The maximum degree to which to compute is computed in terms of the
     degrees of the ring map, ", TT "f", ".  For example, if ", TT "f", "
     consists of cubics, then to find a quadratic relation, this option
     should be set to at least 6, by specifying, for example, ", 
     TT "DegreeLimit => 6", ".  The default is ", TT "infinity", ".",
     SEEALSO {"pushForward1", "DegreeLimit"}
     }

document { pushForward1,
     Headline => "the main computational component of pushForward",
     TT "pushForward1(f,M,options)", " -- Given a ring map f : R --> S, and an S-module
     M, yields a presentation matrix of the R-submodule of M generated by the given
     (S-module) generators of M.",
     PARA,
     "Warning: this function will be removed, and its function incorporated into
     that of ", TO "image", " and ", TO "prune", ".",
     PARA,
     "This is a very basic operation, and is used by several other functions.  See,
     for example, ", TO "pushForward", ".  Therefore we intend to eliminate it,
     and merge its function into ", TO "image", " after introducing
     generalized module homomorphisms which map an R-module to an S-module.",
     PARA,
     "As an example, the following fragment computes the ideal of the
     rational normal curve. This could also be done using ", TO "monomialCurveIdeal", ".",
     EXAMPLE {
	  "R = ZZ/101[a..d];",
      	  "S = ZZ/101[s,t];",
      	  "f = map(S,R,matrix{{s^4, s^3*t, s*t^3, t^4}})",
      	  "pushForward1(f,S^1)",
	  },
     PARA,
     "The following code performs the Groebner computation using a product order 
     rather than the default elimination order.",
     EXAMPLE "pushForward1(f,S^1,MonomialOrder=>ProductOrder)",
     PARA,
     "The computation is stashed inside the ring map, until the computation has
     finished completely.  This means that you may interrupt this command, and 
     later restart it. You may alo obtain partial results, as follows.",
     EXAMPLE {
	  "f = map(S,R,matrix{{s^4, s^3*t, s*t^3, t^4}})",
      	  "pushForward1(f,S^1,DegreeLimit=>4)",
	  },
     "After interrupting a computation (using control-C), you may view the
     equations so far obtained by using the ", TT "PairLimit", " option to prevent any
     further work from being done.",
     EXAMPLE "pushForward1(f,S^1,PairLimit=>0)",
     "The type ", TO "PushforwardComputation", " is used internally by our current implementation.",
     }

document { pushForward1 => StopWithMinimalGenerators,
     Headline => "stop when minimal generators have been determined",
     TT "StopWithMinimalGenerators => true", " -- an option for ", TO "pushForward1", "
     that specifies that the computation should stop as soon as a
     complete list of minimal generators for the submodule or ideal has been
     determined.",
     PARA,
     "The value provided is simply passed on to ", TO "gb", ": see 
     ", TO (gb => StopWithMinimalGenerators), " for details."
     }

document { pushForward1 => PairLimit,
     Headline => "stop when this number of pairs is handled",
     TT "PairLimit => n", " -- keyword for an optional argument used with
     ", TO "pushForward1", ", which specifies that the computation should
     be stopped after a certain number of S-pairs have been reduced."
     }

document { pushForward1 => MonomialOrder,
     Headline => "specify the elimination order to use in pushForward1",
     TT "MonomialOrder => x", " -- a keyword for an optional argument to ", TO "pushForward1", "
     which tells which monomial order to use for the Groebner basis computation
     involved.",
     PARA,
     "Possible values:",
     MENU {
	  (TT "MonomialOrder => EliminationOrder", " -- use the natural elimination order (the default)"),
	  (TT "MonomialOrder => ProductOrder", " -- use the product order"),
	  (TT "MonomialOrder => LexOrder", " -- use lexical order"),
	  },
     SEEALSO "EliminationOrder"
     }

document { pushForward1 => UseHilbertFunction,
     Headline => "whether to use knowledge of the Hilbert function",
     TT "UseHilbertFunction => true", " -- a keyword for an optional argument to
     ", TO "pushForward1", " which specifies whether to use the Hilbert function,
     if one has previously been computed.",
     PARA,
     "The default is to use it if possible."
     }

document { pushForward1 => Strategy,
     Headline => "specify which algorithm to use in the computation",
     TT "pushForward1(f,M,Strategy => v)", " -- an option for ", TO pushForward1, " 
     which can be used to specify the strategy to be used in the computation.",
     PARA,
     "The strategy option value ", TT "v", " should be one of the following.",
     SHIELD MENU {
	  TO "NonLinear",
     	  TO "Linear"
	  },
     PARA,
     "The default is for the code to select the best strategy heuristically."
     }

document { PushforwardComputation,
     Headline => "a type of list used internally by pushForward1",
     TT "PushforwardComputation", " -- a type of list used internally by
     ", TO "pushForward1", "."
     }

document { EliminationOrder,
     Headline => "use the natural elmination order in a pushForward1 computation",
     TT "EliminationOrder", " -- a value for the ", TO "MonomialOrder", "
     option to ", TO "pushForward1", " which specifies the natural elimination
     order be used."
     }


-- Local Variables:
-- compile-command: "make -C $M2BUILDDIR/Macaulay2/m2 "
-- End:
