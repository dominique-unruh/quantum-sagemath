# -*- mode: python; -*-

import itertools
from sage.structure.element import ModuleElement

class SDPModel():
    import mosek.fusion
    def __init__(self):
        self.model = mosek.fusion.Model()
        self.vars = dict()
    def show_stats(self):
        print("{} variables, {} constraints".format(self.model.numVariables(),self.model.numConstraints()))
    def psdMatrix(self,name,dim): # Real matrix
        dim = int(dim)
        vars = SR.var(name,n=dim*dim)
        mosekVar = self.model.variable(name,mosek.fusion.Domain.inPSDCone(dim))
        for i in xrange(dim):
            for j in xrange(dim):
                v = vars[j+dim*i]
                assert v not in self.vars
                self.vars[v] = mosekVar.index(i,j)
        return matrix([[vars[j+dim*i] for j in xrange(dim)] for i in xrange(dim)])
    def solve(self):
        self.model.solve()
    @cached_method
    def solution(self):
        return dict((k,v.level()[0]) for k,v in self.vars.items())
    def show_solution_info(self):
        print("problem status: {}".format(self.model.getProblemStatus()))
        print("solution status: {}".format(self.model.getSolutionStatus()))
        print("primal objective: {}".format(self.model.primalObjValue()))
        print("dual objective: {}".format(self.model.dualObjValue()))
        print(self.model.getProblemStatus())
    def sr2mosek(self,e):
        vars = self.vars
        from mosek.fusion import Expr
        def s2m(e):
                if e.is_symbol():
                    return Expr.mul(int(1),vars[e])
                elif e.operator() == sage.symbolic.operators.add_vararg:
                    return Expr.add([s2m(x) for x in e.operands()])
                elif e.operator() == sage.symbolic.operators.mul_vararg:
                    x,y = e.operands()
                    if x.is_numeric():
                        assert x.is_real()
                        return Expr.mul(float(x),s2m(y))
                    if y.is_numeric():
                        assert y.is_real()
                        return Expr.mul(float(y),s2m(x))
                    raise Exception("Unsupported: multiplication of two expressions: "+str(e))
                elif e.is_numeric():
                    assert e.is_real()
                    return Expr.constTerm(float(e))
                raise Exception("Unsupported expression: "+str(e))
        return s2m(e)
    def addConstraint(self,e,name=None):
        from mosek.fusion import Domain

        if isinstance(e,(list,tuple,set)):
            assert name is None
            return [self.addConstraint(e2) for e2 in e]
        
        if e.is_relational():
            x,y = e.operands()
            if e.operator() == operator.le:
                return self.model.constraint(name, self.sr2mosek(y-x), Domain.greaterThan(int(0)))
            if e.operator() == operator.eq:
                return self.model.constraint(name, self.sr2mosek(y-x), Domain.equalsTo(int(0)))
        return self.model.constraint(name, self.sr2mosek(e), Domain.equalsTo(int(0)))

    
class QuantumHelpers:
    freshvarcounter = 0
    @staticmethod
    def freshVar(assm=False):
        QuantumHelpers.freshvarcounter += 1
        v = SR.symbol("t_{}".format(QuantumHelpers.freshvarcounter))
        #print("Assume",v,"complex")
        if assm: assume(v,'complex') # TODO: Is very slow. Why?
        return v
    @staticmethod
    def freshRealVar(assm=False):
        QuantumHelpers.freshvarcounter += 1
        v = SR.symbol("u_{}".format(QuantumHelpers.freshvarcounter))
        if assm: assume(v,'real')
        return v
    @staticmethod
    def magicsort(tup):
        """Returns a reordered copy of the tup. 
           It is guaranteed that two invocations magicsort(l1),magicsort(l2) 
           return the same tup if l1,l2 are equal as multisets."""
        return tuple(sorted(tup))
    @staticmethod
    def isMagicSorted(tup):
        """Checks whether magicsort(tup)==tup"""
        tup = tuple(tup)
        return QuantumHelpers.magicsort(tup)==tup
    @staticmethod
    def make_exact(base):
        if base in (CDF,RDF):
            return lambda x: base(x)
        elif base in (SR,QQ,QQbar):
            #if real:
                return lambda x: base(QQ(x))
            #else:
            #    return lambda x: QQ(x.real()) + QQ(x.imag()) * I

        raise Exception("Unsupported ring in make_exact: "+str(base))


class QuantumSpace(UniqueRepresentation):
    """A representation of a quantum system with named registers.
       For each register name, there is a named basis."""
    def __init__(self,spaces):
        """spaces is a list of (name,basis) where each name is an arbitrary string (naming a quantum subsystem),
           and basis is a set of values (indexing the basis states of that subsystem)
           
           Example: QuantumSpace((("x",(0,1)),('y',(0,1))))
           for a space with two qubits, called x and y.
           """
        if not isinstance(spaces,tuple):
            raise TypeError("Argument to QuantumSpace(spaces) must be a tuple (use QuantumSpace.make for more flexibility)")
        if not QuantumHelpers.isMagicSorted(spaces):
            raise RuntimeError("Argument to QuantumSpace(spaces) must be sorted according to magicsort (use QuantumSpace.make for more flexibility)")
        self._spaces = tuple(spaces)
        self._spaces_dict = dict(self._spaces)
        if len(self._spaces)!=len(self._spaces_dict):
            raise ValueError("QuantumSpace initialized with non-distinct register names")
        self._size = prod(len(b) for n,b in self._spaces)

        nr_spaces = len(self._spaces)
        basis = []
        basis_dict = {}
        current = list(range(nr_spaces)) # currently constructed basis vector
        def f(i): # iterates over all combinations of subspace-basis vectors for subspaces in self._spaces[i..] and adds them to basis
            if i==nr_spaces:
                curr = tuple(current)
                assert curr not in basis_dict
                basis_dict[curr] = len(basis)
                basis.append(curr)
                return
            (name,space_basis) = self._spaces[i]
            for b in space_basis:
                current[i] = (name,b)
                f(i+1)
        f(0)
        assert len(basis) == self._size
        self._basis = tuple(basis)
        self._basis_dict = basis_dict # Invariant: c in basis_dict iff c in basis,  basis[basis_dict[c]]=c

    def isSubspace(self,other):
        """Is self a subspace of other? That is, is every register of self a register of other, with the same basis?"""
        for n,b in self._spaces:
            if other._spaces_dict.get(n)!=b: return False
        return True
    
    def difference(self,other):
        """Returns the QuantumSpace that contains the registers that self contains, but other does not.
        
           Raises an exception if other and self share a register of the same name, but with different basis.
        """
        spaces = self._spaces_dict.copy()
        for n,b in other._spaces:
            b2 = spaces.get(n)
            if b2 is not None:
                if b!=b2: raise RuntimeError("Register {} has different bases {} vs {}".format(n,b2,b))
                #print("DEL {}".format(n))
                del spaces[n]
        return QuantumSpace.make(spaces)

    @staticmethod
    def make(spaces):
        """Like QuantumSpace(spaces), except that QuantumSpace.make(spaces) also accepts arguments that are lists or dictionaries, not tuples"""
        if isinstance(spaces,dict): spaces = QuantumHelpers.magicsort(spaces.items())
        return QuantumSpace(tuple( (n,tuple(a)) for (n,a) in spaces ))
        
    def basis(self):
        return self._basis

    def dimension(self): return self._size

    def basis_to_idx(self,b):
        return self._basis_dict[b]

    @staticmethod
    def pretty_basis_element(elem):
        return "|{}>_{}".format(",".join(str(b) for n,b in elem),
                                "".join(n for n,b in elem))
    @staticmethod
    def latex_basis_element(elem):
        return r"\left\vert{}\right\rangle_{{{}}}".format(",".join(latex(b) for n,b in elem),
                                               "".join(n for n,b in elem))

    @staticmethod
    def pretty_basis_butterfly(elem1,elem2):
        return "{}_|{}><{}|_{}".format("".join(n for n,b in elem1),
                                       ",".join(str(b) for n,b in elem1),
                                       ",".join(str(b) for n,b in elem2),
                                       "".join(n for n,b in elem2))

    @staticmethod
    def latex_basis_butterfly(elem1,elem2):
        return r"\left\vert {} \right\rangle_{{{}}}  \left\langle {} \right\vert_{{{}}}".format(
                                       ",".join(str(b) for n,b in elem1),
                                       "".join(n for n,b in elem1),
                                       ",".join(str(b) for n,b in elem2),
                                       "".join(n for n,b in elem2))

    def pretty_basis(self):
        return [QuantumSpace.pretty_basis_element(item) for item in self.basis()]

    def short_description(self): return ",".join(n+":"+str(len(b)) for n,b in self._spaces)
    def __str__(self):
        return "QuantumSpace({})".format(self.short_description())
    def __repr__(self): return self.__str__()
    def tensor(self,other):
        return self.tensor_and_maps(other)[0]
    @cached_method
    def tensor_and_maps(self,other):
        """Like tensor(self,other), but additionally provides morphisms from 
        the product space back to self and other.

        Returns:
        prod - the tensor product space
        morph1 - morphism from space to self
        morph2 - morphism from space to other
        """

        print "Creating tensor product space"
        assert(isinstance(other,QuantumSpace)), "QuantumSpace.tensor: "+str(other)+" not of type QuantumSpace"
        if not set(self._spaces_dict.keys()).isdisjoint(other._spaces_dict.keys()):
            raise ValueError("Tensor product of spaces with non-disjoint registers attempted")
        prod = QuantumSpace(QuantumHelpers.magicsort(self._spaces + other._spaces))
        _,morph1 = prod.remove_and_maps(other.registerNames())
        _,morph2 = prod.remove_and_maps(self.registerNames())
        return (prod,morph1,morph2)
    def remove(self,remove):
        return self.remove_and_maps(remove)[0]
    @cached_method
    def remove_and_maps(self,remove):
        """Like remove, but additionally returns morphisms from the original 
        space to the one after removal. (E.g., |xyz>_ABC might be mapped to |xy>_AB.).

        Returns:
        space - the smaller QuantumSpace
        morph - a QuantumBasisMap from self to space
        """
        if isinstance(remove,str): remove = (remove,)
        for i in remove: assert i in self._spaces_dict, i
        def filter(x):
            return tuple((n,i) for (n,i) in x if n not in remove)
        newSpace = QuantumSpace(filter(self._spaces))
        m = tuple((b,filter(b)) for b in self.basis())
        morph = QuantumBasisMap(self,newSpace,m)
        return (newSpace,morph)
    def renameRegisters(self,f):
        """Creates a new QuantumSpace, with registers renamed according to f.
           f can be a function or a dictionary.

           Returns: qs - The new space
                    m1 - The morphism from self to qs
                    m2 - The morphism from qs to self
        """
        f2 = (lambda n: f.get(n,n)) if isinstance(f,dict) else f
        qs = QuantumSpace(QuantumHelpers.magicsort(tuple((f2(n),a) for n,a in self._spaces)))
        fdict = tuple((n, f2(n)) for n,a in self._spaces)
        finv = tuple((f2(n), n) for n,a in self._spaces)

        m1 = QuantumRegisterMap(self,qs,fdict)
        m2 = QuantumRegisterMap(qs,self,finv)
        return (qs,m1,m2)
    def registerNames(self):
        return tuple(n for n,a in self._spaces)

class QuantumRegisterMap(UniqueRepresentation):
    def __init__(self,src,target,nameMap):
        self._nameMap = dict(nameMap)
        self._src = src
        self._target = target
#        self._indexMap = dict((src.basis_to_idx(b), target.basis_to_idx(self(b)))
#                              for b in self._src.basis())
    def __call__(self,elem):
        m = self._nameMap
        return QuantumHelpers.magicsort(tuple((m[n],x) for n,x in elem))
    def operator(self,base):
        space = QuantumOperatorSpace(base,self._src,self._target)
        map = [(self._target.basis_to_idx(self(b)), self._src.basis_to_idx(b))
               for b in self._src.basis()]
        #print("MAP",map)
        m = matrix(SR,self._src.dimension(),self._target.dimension(),dict((ij,1) for ij in map))
        #print(m)
        return space(m)


class QuantumBasisMap(UniqueRepresentation):
    def __init__(self,src,target,basisMap):
        self._basisMap = dict(basisMap)
        self._src = src
        self._target = target
        self._indexMap = dict((src.basis_to_idx(b), target.basis_to_idx(self(b)))
                              for b in self._src.basis())
    def __call__(self,elem):
        return self._basisMap[elem]
    def map_index(self,index):
        return self._indexMap[index]


EmptyQuantumSpace = QuantumSpace(tuple())

class QuantumVector(ModuleElement):
    """An element of QuantumVectorSpace(...)"""
    def __init__(self,parent,vector):
        ModuleElement.__init__(self,parent)
        self._vector = vector

    def __repr__(self):
        space = self.parent().space()
        components = []
        for b,x in zip(space.pretty_basis(),self._vector):
            if x==0: continue
            #components.append("{}⋅∣{}⟩".format(x,b))
            if x==1:
                components.append(b)
            else:
                components.append("{} {}".format(x,b))
        if not components: return '0'
        return " + ".join(components)
    def _latex_(self):
        space = self.parent().space()
        components = []
        for b,x in zip(space.basis(),self._vector):
            if x==0: continue
            #components.append("{}⋅∣{}⟩".format(x,b))
            if x==1:
                components.append(space.latex_basis_element(b))
            else:
                components.append("{}\, {}".format(latex(x),space.latex_basis_element(b)))
        if not components: return '0'
        return " + ".join(components)
    def _lmul_(self,x):
        return QuantumVector(self.parent(), self._vector._lmul_(x))
    def _rmul_(self,x):
        return QuantumVector(self.parent(), self._vector._rmul_(x))
    def _add_(self,x):
        return QuantumVector(self.parent(), self._vector._add_(x._vector))
    def _neg_(self):
        return QuantumVector(self.parent(), -self._vector)
    def vector(self):
        return self._vector
    def as_ket_operator(self):
        opspace = QuantumOperatorSpace(self.parent().base(),EmptyQuantumSpace,self.parent().space())
        return opspace(matrix(self._vector).transpose())
    def as_bra_operator(self):
        opspace = QuantumOperatorSpace(self.parent().base(),self.parent().space(),EmptyQuantumSpace)
        m = matrix(self._vector)
        for i in range(m.ncols()): m[0,i] = conjugate(m[0,i])
        return opspace(m)
    def inner(self,other):
        """Inner product"""
        assert self.parent()==other.parent()
        return sum(conjugate(x)*y for x,y in zip(self.vector(),other.vector()))
    def density_op(self):
        """Returns this state as a density operator. Equivalently, the orthogonal projector onto this state."""
        opspace = QuantumOperatorSpace(self.parent().base(),self.parent().space(),self.parent().space())
        m1 = matrix(self._vector)
        for i in range(m1.ncols()): m1[0,i] = conjugate(m1[0,i])
        m2 = matrix(self._vector).transpose()
        return opspace(m2*m1)
    def tensor(self,other):
        raise Exception("Wrong implementation: needs to take into account basis reordering")
        parent = self.parent().tensor(other.parent())
        v1 = self.vector()
        v2 = other.vector()
        v = []
        for x in v1:
            for y in v2:
                v.append(x*y)
        return parent(v)
    def norm(self,p=2):
        return self._vector.norm(p)
    def normalize(self):
        return self/self.norm()
    def substitute(self,map):
        raise NotImplemented("QuantumOperator.substitute")
    def __eq__(self,other):
        if not isinstance(other,QuantumVector): return False
        if other.parent() != self.parent(): return False
        return self.vector() == other.vector()
    def __ne__(self,other):
        return not (self==other)


class QuantumVectorSpace(sage.structure.parent.Parent,UniqueRepresentation):
    """QuantumVectorSpace(F,Q) -- A complex vector space over field K and with the canonical basis associated with QuantumSpace Q"""
    Element = QuantumVector
    def __init__(self,K,space):
        self._space = space
        self._vector_parent = VectorSpace(K,space.dimension())
        #category = sage.categories.modules.Modules.FiniteDimensional
        sage.structure.parent.Parent.__init__(self)
        #self._populate_coercion_lists_(action_list=[sage.structure.coerce_actions.LeftModuleAction(K,self)])
    def _element_constructor_(self,*args,**kwargs):
        if len(args)==1 and not kwargs:
            return self.element_class(self,self._vector_parent(args[0]))
        elif len(args)==1 and (args[0]==0 or args[0] is None) and kwargs:
            return self.from_dict(kwargs)
        else:
            print(args); print(kwargs)
            raise RuntimeError("invalid arguments")
    def from_dict(self,d):
        space = self._space
        for k in d.keys():
            assert k in space._spaces_dict
        basis_idx = tuple((n,d[n]) for n,tmp in space._spaces)
        idx = space.basis_to_idx(basis_idx)
        vec = space.dimension()*[0]
        vec[idx] = 1
        return self.element_class(self,self._vector_parent(vec))
    def from_basis_name(self,b):
        idx = self._space.basis_to_idx(b)
        vec = self._space.dimension()*[0]
        vec[idx] = 1
        return self.element_class(self,self._vector_parent(vec))
    def basis_element(self,**kwargs):
        """Returns a basis state. E.g. basis_element(x=0,y=1) gives the state ket(01) on registers x,y"""
        return self.from_dict(kwargs)
    def space(self): return self._space
    def base(self): return self._vector_parent.base()
    #def _indices(self): nyi()
    def tensor(self,other):
        return self.tensor_and_maps(other)[0]
    @cached_method
    def tensor_and_maps(self,other):
        print "Creating tensor vector product space:", self, other
        if self.base() != other.base():
            raise TypeError("Tensor product of vector spaces with different bases")
        if not isinstance(self,QuantumVectorSpace):
            raise TypeError("Second argument of tensor product must be a QuantumVectorSpace, too")
        prod,m1,m2 = self.space().tensor_and_maps(other.space())
        vs = QuantumVectorSpace(self.base(), prod)
        return (vs, m1, m2)
    def __repr__(self):
        return "QuantumVectorSpace({})".format(self.space().short_description())
    def __str__(self):
        return self.__repr__()
    def dimension(self):
        return self._space.dimension()
    def random(self):
        """Returns a random non-zero vector (the distribution is not specified)"""
        base = self.base()
        dim = self.dimension()
        vec = 0
        while vec==0:
            vec = random_vector(ring=base, degree=dim, bound=100)
        return self(vec)
    def random_unit(self,real=False,skip_normalize=False):
        """Returns a random vector of length 1 (Haar measure).
        If real=True, returns a real-valued vector."""
        # TODO: could use sage.probability.probability_distribution.SphericalDistribution
        dim = self.dimension()
        gauss = RealDistribution('gaussian', 1)

        #print("BASE",self.base())
        mk_qq = QuantumHelpers.make_exact(self.base())
        
        if real:
            vec = self([mk_qq(gauss.get_random_element()) for i in xrange(dim)])
        else:
            vec = self([mk_qq(gauss.get_random_element())+mk_qq(gauss.get_random_element())*I for i in xrange(dim)])
        return vec if skip_normalize else vec.normalize()
    # def random_unit_real(self):
    #     """Returns a random real vector of length 1 (Haar measure)"""
    #     # TODO: sage.probability.probability_distribution.SphericalDistribution
    #     dim = self.dimension()
    #     gauss = RealDistribution('gaussian', 1)
    #     vec = self([gauss.get_random_element() for i in range(dim)])
    #     return vec.normalize()
    def generic(self):
        assert self.base()==SR
        dim = self.dimension()
        v = [QuantumHelpers.freshVar() for i in range(dim)]
        return self(v)
    def identity_on(self):
        space = self.space()
        return QuantumOperatorSpace(self.base(),space,space).identity()
    def hadamard(self):
        if self.dimension()!=2:
            raise TypeError("Hadamard only supported for two-dimensional vector spaces")
        space = self.space()
        return QuantumOperatorSpace(self.base(),space,space).hadamard()
    def random_orthonormal_set(self,n,real=False):
        dim = self.dimension()
        if n > dim:
            raise TypeError("Cannot construct more orthonormal vectors than dimension")
        vectors = [self.random_unit(real=real).vector() for i in range(n)]
        vec_matrix = matrix(self.base(),vectors)
        G, M = vec_matrix.transpose()._gram_schmidt_noscale()
        assert G.nrows() == dim
        assert G.ncols() == n
        return [self(v).normalize() for v in G.columns()]
    # def random_orthonormal_set_real(self,n):
    #     if self.base()==CDF or self.base()==RDF:
    #         mk_qq = lambda x: x
    #     else:
    #         mk_qq = lambda x: QQ(x.real())
        
    #     dim = self.dimension()
    #     if n > dim:
    #         raise TypeError("Cannot construct more orthonormal vectors than dimension")
    #     vectors = [[mk_qq(x) for x in self.random_unit_real().vector()] for i in range(n)]
    #     vec_matrix = matrix(self.base(),vectors)
    #     G, M = vec_matrix.transpose()._gram_schmidt_noscale()
    #     assert G.nrows() == dim
    #     assert G.ncols() == n
    #     return [self(v).normalize() for v in G.columns()]
    @staticmethod
    def make(K,spaces):
        return QuantumVectorSpace(K,QuantumSpace.make(spaces))


class QuantumOperator(ModuleElement):
    """An element of QuantumOperatorSpace(...)"""
    def __init__(self,parent,matrix):
        ModuleElement.__init__(self,parent)
        self._matrix = matrix

    def substitute(self,map):
        parent = self.parent()
        matrix = self.matrix()
        return parent(matrix.substitute(map))

    def __repr__(self):
        domain = self.parent().domain()
        codomain = self.parent().codomain()
        matrix = self._matrix
        components = []
        for b_col,col in zip(domain.basis(),itertools.count()):
            for b_row,row in zip(codomain.basis(),itertools.count()):
                x = matrix[row,col]
                if x==0: continue
                butterfly = QuantumSpace.pretty_basis_butterfly(b_row,b_col)
                if x==1:
                    components.append(butterfly)
                else:
                    components.append("{} {}".format(x,butterfly))
        if not components: return '0'
        return " + ".join(components)
    def _latex_(self):
        domain = self.parent().domain()
        codomain = self.parent().codomain()
        matrix = self._matrix
        components = []
        for b_col,col in zip(domain.basis(),itertools.count()):
            for b_row,row in zip(codomain.basis(),itertools.count()):
                x = matrix[row,col]
                if x==0: continue
                butterfly = QuantumSpace.latex_basis_butterfly(b_row,b_col)
                if x==1:
                    components.append(butterfly)
                else:
                    components.append("{}\,{}".format(latex(x),butterfly))
        if not components: return '0'
        return " + ".join(components)

    def _lmul_(self,x): # Only for scalar multiplication?
        return QuantumOperator(self.parent(), self._matrix._lmul_(x))
    def _rmul_(self,x): # Only for scalar multiplication?
        return QuantumOperator(self.parent(), self._matrix._rmul_(x))
    def __mul__(self,x):
        if self.parent()==x.parent() and self.parent().domain() == x.parent().codomain():
            return self.multiply(x)
        else:
            return super(QuantumOperator,self).__mul__(x)
    def _add_(self,x):
        assert self.parent().base() == x.parent().base()
        return QuantumOperator(self.parent(), self._matrix._add_(x._matrix))
    def _neg_(self):
        return QuantumOperator(self.parent(), -self._matrix)
    def matrix(self):
        return self._matrix
    def adjoint(self):
        matrix = self._matrix.transpose()
        for i in range(matrix.nrows()):
            for j in range(matrix.ncols()):
                matrix[i,j] = conjugate(matrix[i,j])
        parent = self.parent().adjoint()
        return parent(matrix)
    def multiply(self,x):
        #print("MULTIPLY",type(x))
        assert isinstance(x,QuantumOperator), type(x)
        assert self.parent().domain() == x.parent().codomain(), (self.parent().domain(), x.parent().codomain())
        assert self.parent().base() == x.parent().base(), (self.parent().base(), x.parent().base())
        opspace = QuantumOperatorSpace(self.parent().base(), x.parent().domain(), self.parent().codomain())
        return opspace(self._matrix * x._matrix)
    def multiplyVector(self,x):
        #print("MULTIPLY VECTOR",type(x))
        assert isinstance(x,QuantumVector), type(x)
        assert self.parent().domain() == x.parent().space(), (self.parent().domain(), x.parent().space())
        assert self.parent().base() == x.parent().base(), (self.parent().base(), x.parent().base())
        vs = QuantumVectorSpace(self.parent().base(), self.parent().codomain())
        return vs(self._matrix * x._vector)
    def equations(self, dont_filter=False): # Returns a set of equations over the base field, equivalent to self==0
        eqs = []
        m = self._matrix
        for i in range(m.nrows()):
            for j in range(m.ncols()):
                x = m[i,j]
                if (not dont_filter) and x==0: continue
                eqs.append(x)
        return eqs
    def isHermiteanEqs(self):
        return (self-self.adjoint()).equations()
    def isPositiveSemidefiniteIneqs(self):
        """Returns a list of ineqalities that are simultaneously true iff this operator is positive semidefinite.

        All inequalities are of the form term>=0 or term==0 or False.

        If the operator contains only numeric entries, the result will be [] (i.e., is positive semidefinite) or [False] (i.e., isn't positive semidefinite).
        """
        M = self.matrix()
        assert M.nrows() == M.ncols()
        def minors(n): # Returns all empty subtuples of (0..n-1)
            tuples = [[]]
            for i in range(n):
                for t in list(tuples):
                    tuples.append(t + [i,])
            return tuples
        eqs = []
        for e in self.isHermiteanEqs():
            if e.is_numeric():
                if e != 0: return [False]
            else:
                eqs.append(e==0)
        for rc in minors(M.nrows()):
            minor = M.matrix_from_rows_and_columns(rc,rc)
            det = minor.determinant()
            print(det)
            if (det >= 0): print(">=")
            elif (det < 0): return [False]
            else: eqs.append(simplify(det) >= 0)
        return eqs
    def tensor(self,other):
        parent,dm1,dm2,cm1,cm2 = self.parent().tensor_and_maps(other.parent())
        m1 = self.matrix()
        m2 = other.matrix()
        ddim = parent.domain().dimension()
        cdim = parent.codomain().dimension()
        m = matrix(parent.base(), cdim, ddim)
        for row in xrange(cdim):
            row1 = cm1.map_index(row)
            row2 = cm2.map_index(row)
            for col in xrange(ddim):
                col1 = dm1.map_index(col)
                col2 = dm2.map_index(col)
                m[row,col] = m1[row1,col1] * m2[row2,col2]
        # for row1 in m1:
        #     for row2 in m2:
        #         row = []
        #         for x in row1:
        #             for y in row2:
        #                 row.append(x*y)
        #         m.append(row)
        return parent(m)
    def trace(self):
        parent = self.parent()
        assert parent.domain() == parent.codomain()
        return self.matrix().trace()
    def partial_trace(self,remove):
        """Partial trace of this operator.
        
        remove = names of quantum registers to remove"""
        if isinstance(remove,str): remove = (remove,)
        parent = self.parent()
        base = parent.base()
        remove = frozenset(remove)
        dom = parent.domain()
        codom = parent.codomain()
        target_dom = dom.remove(remove)
        target_codom = codom.remove(remove)
        target = QuantumOperatorSpace(base,target_dom,target_codom)
        def split(origspace,targetspace,b):
            keep = tuple((n,i) for (n,i) in b if n not in remove)
            keep = targetspace.basis_to_idx(keep)
            drop = tuple((n,i) for (n,i) in b if n in remove)
            orig = origspace.basis_to_idx(b)
            return (keep,drop,orig)
        domain = [split(dom,target_dom,b) for b in parent.domain().basis()]
        codomain = [split(codom,target_codom,b) for b in parent.codomain().basis()]
        #print domain
        #print codomain
        selfm = self.matrix()
        m = [[0 for i in xrange(target_dom.dimension())] for j in xrange(target_codom.dimension())]
        for (rowkeep,rowdrop,row) in codomain:
            for (colkeep,coldrop,col) in domain:
                if coldrop == rowdrop:
                    m[rowkeep][colkeep] += selfm[(row,col)]
        return target(m)
    def change_base(self,base):
        ops = self.parent().change_base()
        return ops(self.matrix())
    
    def extend(self,op_space):
        """Extends self to the larger operator space op_space.
        Returns o=self.tensor(identity) for a suitably large identity (such that o is in op_space).
        Requires that op_space adds the same registers to domain/codomain of self.parent().
        """
        assert isinstance(op_space,QuantumOperatorSpace), "QuantumOperator.extend: "+str(op_space)+" not of type QuantumOperatorSpace"
        parent = self.parent()
        assert parent.domain().isSubspace(op_space.domain()), "QuantumOperator.extend: domain "+str(parent.domain())+" not a subspace of "+str(op_space.domain())
        assert parent.codomain().isSubspace(op_space.codomain()), "QuantumOperator.extend: codomain "+str(parent.codomain())+" not a subspace of "+str(op_space.codomain())
        extra = op_space.domain().difference(parent.domain())
        assert extra == op_space.codomain().difference(parent.codomain())
        identity_ops = QuantumOperatorSpace(parent.base(),extra,extra)
        identity = identity_ops.identity()
        return self.tensor(identity)
    def eigenvalues(self):
        """Returns the eigenvalues of this operator as a list (eigenvalues of higher multiplicity are repeated)."""
        return self.matrix().eigenvalues()
    def trace_norm(self):
        return sum(abs(x) for x in self.eigenvalues())
    def trace_distance(self,other):
        return (self-other).trace_norm()/2
    def __eq__(self,other):
        if not isinstance(other,QuantumOperator): return False
        if other.parent() != self.parent(): return False
        return self.matrix() == other.matrix()
    def __ne__(self,other):
        return not (self==other)
    def kernel_orthogonal_basis(self):
        """Returns an orthogonal basis of the right kernel of this operator.
        In case of base ring SR, it only works if all entries can be cast to QQbar (no symbolic entries)"""
        M = self.matrix()
        if self.parent().base()==SR: M = matrix(QQbar,M)
        B = list(M.right_kernel().matrix().gram_schmidt()[0])
        dom = self.parent().domain_vs()
        return [dom(b) for b in B]
    def kernel_onb(self):
        """Returns an orthonormal basis of the right kernel of this operator.
        Only works if all entries can be cast to QQbar (no symbolic entries)"""
        return [b.normalize() for b in self.kernel_orthogonal_basis()]
    def kernel_projector(self):
        """Returns a projector onto the right kernel of this operator."""
        return sum(b.density_op() for b in self.kernel_onb())
    def subs(self,in_dict=None,**kwds):
        return self.parent()(self.matrix().subs(in_dict,**kwds))
    def map(self,f):
        M = [[f(x) for x in row] for row in self.matrix()]
        return self.parent()(M)
    def numerical_approx(self, prec=None, digits=None, algorithm=None):
        M = self.matrix().n(prec,digits,algorithm)
        parent = self.parent()
        space = QuantumOperatorSpace(M.parent().base(), parent.domain(), parent.codomain())
        return space(M)
    def change_base(self, base):
        return QuantumOperator(self.parent().change_base(base), matrix(base, self.matrix()))
    

class QuantumOperatorSpace(sage.structure.parent.Parent,UniqueRepresentation):
    """QuantumOperatorSpace(F,Q) -- Space of linear operators on QuantumVectorSpace(F,Q)"""
    Element = QuantumOperator
    def __init__(self, K, domain, codomain):
        if not isinstance(domain,QuantumSpace): raise TypeError("domain is not a quantum space ({} is a {})".format(domain,type(domain)))
        if not isinstance(codomain,QuantumSpace): raise TypeError("codomain is not a quantum space ({} is a {})".format(codomain,type(codomain)))

        self._domain = domain
        self._codomain = codomain
        self._field = K
        self._matrix_parent = MatrixSpace(K,codomain.dimension(),domain.dimension())
        sage.structure.parent.Parent.__init__(self)
        #self._populate_coercion_lists_(action_list=[sage.structure.coerce_actions.LeftModuleAction(K,self)])
    def _element_constructor_(self,*args,**kwargs):
        if len(args)==1 and not kwargs:
            x = args[0]
            return self.element_class(self,self._matrix_parent(x))
        else:
            print(args); print(kwargs)
            raise RuntimeError("invalid arguments")
    def domain(self): return self._domain
    def codomain(self): return self._codomain
    def base(self): return self._matrix_parent.base()
    def adjoint(self):
        return QuantumOperatorSpace(self._field,self._codomain,self._domain)
    def domain_vs(self): return QuantumVectorSpace(self._field,self._domain)
    def codomain_vs(self): return QuantumVectorSpace(self._field,self._codomain)
    def __repr__(self):
        return "QuantumOperatorSpace({},{},{})".format(self.base(),self.domain(),self.codomain())

    class MulAction(sage.categories.action.Action):
        def __init__(self, A, B):
            self._codomain = QuantumOperatorSpace(A.base(),B.domain(),A.codomain())
            sage.categories.action.Action.__init__(self, A, B, True, operator.mul)
        def _call_(self, a, b):
            return a.multiply(b)
        def codomain(self):
            return self._codomain
    class MulVecAction(sage.categories.action.Action):
        def __init__(self, A, B):
            self._codomain = QuantumVectorSpace(A.base(), A.codomain())
            sage.categories.action.Action.__init__(self, A, B, True, operator.mul)
        def _call_(self, a, b):
            return a.multiplyVector(b)
        def codomain(self):
            return self._codomain
    def _get_action_(self,S,op,self_on_left):
        #print("GA",op,self.domain(),self.base,S.base())
        if self_on_left \
            and op==operator.mul \
            and isinstance(S,QuantumOperatorSpace) \
            and self.domain() == S.codomain() \
            and self.base() == S.base():
                return QuantumOperatorSpace.MulAction(self,S)
        if self_on_left \
            and op==operator.mul \
            and isinstance(S,QuantumVectorSpace) \
            and self.domain() == S.space() \
            and self.base() == S.base():
                return QuantumOperatorSpace.MulVecAction(self,S)
    def tensor(self,other):
        return self.tensor_and_maps(other)[0]
    @cached_method
    def tensor_and_maps(self,other):
        print "Creating tensor operator product space:", self, other
        if self.base() != other.base():
            raise TypeError("Tensor product of operator spaces over different fields")
        if not isinstance(other,QuantumOperatorSpace):
            raise TypeError("Second argument of tensor product must be a QuantumOperatorSpace, too")
        domprod,dm1,dm2 = self.domain().tensor_and_maps(other.domain())
        codomprod,cm1,cm2 = self.codomain().tensor_and_maps(other.codomain())
        os = QuantumOperatorSpace(self.base(), domprod, codomprod)
        return (os,dm1,dm2,cm1,cm2)
    def generic(self):
        assert self.base()==SR
        rows = self.codomain().dimension()
        cols = self.domain().dimension()
        M = [[QuantumHelpers.freshVar() for i in range(cols)] for j in range(rows)]
        return self(M)
    def generic_sdp(self,sdp_var):
        rows = self.codomain().dimension()
        cols = self.domain().dimension()
        M = sum(matrix(RR,rows,cols,{(i,j):1}) * sdp_var[i,j] for i in range(cols) for j in range(rows))
        return M # Can't return self(M) because M does not lie in MatrixSpace(something), but instead has a strange parent
    def genericPositiveSemidefinite(self):
        assert self.base()==SR
        assert self.domain()==self.codomain()
        dim = self.domain().dimension()
        op = self.generic()
        return op.adjoint() * op
        #return sum( self.domain_vs().generic().density_op() for i in range(dim) )
    def sdpPositiveSemidefiniteReal(self,model,name):
        """Creates an operator backed up by a variable in the SDPModel model.
        The operator is assumed to be >=0 and real."""
        assert isinstance(model,SDPModel)
        assert self.domain()==self.codomain()
        dim = self.domain().dimension()
        M = model.psdMatrix(name,dim)
        return self.change_base(SR)(M)
    def genericHermitean(self):
        assert self.base()==SR
        assert self.domain()==self.codomain()
        dim = self.domain().dimension()
        M = [[None for i in range(dim)] for j in range(dim)]
        for i in range(dim):
            for j in range(dim):
                if i==j:
                    M[i][j] = QuantumHelpers.freshRealVar()
                elif i<j:
                    M[i][j] = QuantumHelpers.freshVar()
                else:
                    M[i][j] = conjugate(M[j][i])
        return self(M)
        return sum( self.domain_vs().generic().density_op() for i in range(dim) )
    def identity(self):
        assert(self.domain()==self.codomain())
        return self(matrix.identity(self.domain().dimension()))
    def change_base(self,base):
        return QuantumOperatorSpace(base,self.domain(),self.codomain())
    def hadamard(self):
        if self.domain().dimension()!=2:
            raise TypeError("Hadamard only supported for two-dimensional vector spaces")
        if self.codomain().dimension()!=2:
            raise TypeError("Hadamard only supported for two-dimensional vector spaces")
        return self([[1/sqrt(2),1/sqrt(2)],[1/sqrt(2),-1/sqrt(2)]])
    def random_isometry(self,real=False):
        """Returns a uniformly random isometry (Haar measure).
        If real=True, a real-valued isometry is chosen."""
        dim1 = self.domain().dimension()
        dim2 = self.codomain().dimension()
        codomain_vs = self.codomain_vs()
        if dim1 > dim2:
            raise TypeError("Cannot construct isometries for operator spaces with domain larger than codomain")
        vectors = codomain_vs.random_orthonormal_set(dim1,real=real)
        U = matrix([v.vector() for v in vectors]).transpose()
        return self(U)
    def random_projector(self,rank,real=False):
        assert rank >= 0
        dim1 = self.domain().dimension()
        dim2 = self.codomain().dimension()
        assert dim1 == dim2
        assert rank <= dim1
        base = self.base()
        
        U = self.random_isometry(real=real)
        P = self(matrix.diagonal(base, [1 if i<rank else 0 for i in xrange(dim1)]))

        return U*P*U.adjoint()
    # def random_isometry_real(self):
    #     dim1 = self.domain().dimension()
    #     dim2 = self.codomain().dimension()
    #     codomain_vs = self.codomain_vs()
    #     if dim1 > dim2:
    #         raise TypeError("Cannot construct isometries for operator spaces with domain larger than codomain")
    #     vectors = codomain_vs.random_orthonormal_set_real(dim1)
    #     U = matrix([v.vector() for v in vectors]).transpose()
    #     return self(U)
    def change_base(self, base):
        return QuantumOperatorSpace(base, self.domain(), self.codomain())
