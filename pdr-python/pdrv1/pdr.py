from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV, EqualsOrIff
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.shortcuts import Interpolator
from pysmt.logics import QF_BV
import heapq

class TransitionSystem(object):
    """Trivial representation of a Transition System."""
    def __init__(self, variables, prime_variables, init, trans):
        self.variables = variables
        self.prime_variables = prime_variables
        self.init = init
        self.trans = trans # T -> 

def next_var(v):
    """Returns the 'next' of the given variable"""
    return Symbol("%s_prime" % v.symbol_name(), v.symbol_type())

class BaseAddrCnt(TransitionSystem):
    def __init__(self, nbits):
        self.nbits = nbits # save the number of bits
        self.mask = 2**(nbits)-1

        base = Symbol('base', BVType(nbits))
        addr = Symbol('addr', BVType(nbits))
        cnt  = Symbol('cnt',  BVType(nbits))
        inp  = Symbol('inp',  BVType(nbits))
        lden = Symbol('lden',  BVType(1))

        self.base = base 
        self.addr = addr 
        self.cnt  = cnt  
        self.inp  = inp  
        self.lden = lden 


        variables = [base, addr, cnt, inp, lden]
        prime_variables = [next_var(v) for v in variables]
        init = base.Equals(0) & addr.Equals(0) & cnt.Equals(0)
        trans= next_var(base).Equals( \
            Ite(lden.Equals(1), inp, base  )) & \
            next_var(addr).Equals( \
            Ite(lden.Equals(1), inp, BVAdd(addr, BV(1, nbits) ) )) & \
            next_var(cnt).Equals( \
            Ite(lden.Equals(1), BV(0, nbits), BVAdd(cnt, BV(1, nbits) ) ))
            
        TransitionSystem.__init__(self, \
          variables = variables, \
          prime_variables = prime_variables, \
          init = init, trans = trans )

    def neq_property(self, base, addr, cnt):
        addr = addr & self.mask
        base = base & self.mask
        cnt  = cnt  & self.mask

        assert ( addr !=  ((base+cnt) & self.mask) )

        return Not( self.addr.Equals(addr) & self.base.Equals(base) & self.cnt.Equals(cnt) )



class PDR(object):
    def __init__(self, system):
        self.system = system
        self.frames = [ [system.init], []  ] # list of list of clauses
        self.solver = Solver()
        self.itp_solver = Interpolator(logic=QF_BV)
        self.prime_map = dict([(v, next_var(v)) for v in self.system.variables])
        self.primal_map = dict([(next_var(v), v) for v in self.system.variables])
        self.cexs_blocked = {}  # <n, cex> : n -> list of cex, maybe blocked already
        self.unblockable_fact = {} # <n, ex> : n -> list of ex, unblocked, used to syn
        # map: v --> next_v

    def check_property(self, prop, remove_vars = [], keep_vars = None):
        """Property Directed Reachability approach without optimizations."""
        print("Checking property %s." % prop)

        while True:
            self.sanity_check_frame_monotone()

            # frame[-1] /\ T -> not (prop)
            cube = self.get_bad_state_from_property_invalid_after_trans(prop, -1, remove_vars, keep_vars)

            print ('Get cube: ', cube , ' @F%d' % (len(self.frames)-1))
            # cube is list of (var, assignments)
            if cube is not None:
                # Blocking phase of a bad state
                if not self.recursive_block(cube, len(self.frames)-1, remove_vars, keep_vars ):
                    print("--> Bug found at step %d" % (len(self.frames)))
                    break
                else:
                    print("   [PDR] Cube blocked '%s'" % self.print_cube(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.is_last_two_frames_inductive():
                    print("--> The system is safe, frame : %d" % len(self.frames) )
                    break
                else:
                    print("   [PDR] Adding frame %d..." % (len(self.frames)))
                    self.frames.append([])
                    self.push_lemma_from_last_frame(remove_vars, keep_vars) # TODO
                    # you should try to push existing clauses
    
    # TODO: problem : INIT -> next frame ????
    # put too few in the          
    def push_lemma_from_last_frame(self, remove_vars, keep_vars):
        # push cex_blocked ?
        fidx = len(self.frames)-1 # the last frame
        print ('Try pushing lemma F%d -> F%d ' % (fidx-1, fidx))
        for cex in self.cexs_blocked[fidx-1]:
            if self.recursive_block(cex, fidx, remove_vars, keep_vars):
                self.cexs_blocked[fidx].append(cex)
        print ('cexs[%d]' % fidx , self.cexs_blocked[fidx])  # has repeated cexs ??/ BUG
        assert (False)
        # push itp ?
        lemmas_to_try = self.frames[fidx-1][:] # make a copy
        for lemma in lemmas_to_try:
            #F[fidx-1] /\ T => lemma ?
            print ('Try pushing lemma to F%d: ' % fidx , str(lemma))
            ex = self.get_bad_state_from_property_invalid_after_trans(lemma, fidx-1, remove_vars, keep_vars )
            if ex is None: # no bad state, lemma is still valid
                self.frames[fidx].append(lemma)
                print ('Succeed!')
            else:
                if self.recursive_block(ex, fidx-1, remove_vars, keep_vars ):
                    lemmas_to_try.append(lemma)
                    # if blocked so what? retry
                else:
                    if fidx-1 not in self.unblockable_fact:
                        self.unblockable_fact[fidx-1] = []
                    self.unblockable_fact[fidx-1].append(ex)
                    print ('fail due to fact' , self.print_cube(ex))
                    # Question:  lemma (for each lemma control the sygus upper bound, expr size, trial no)

                    # get the variable of ex
                    # get the operators of lemma
                    # get the unblockable fact of these variables
                    #    and all other with more variables, 
                    # get the cexs of these variables or fewer
                    # sygus  --- what if there are conflicts???
                    # get back and put to 

                    # but if you try with F[fidx - 1] /\ T --> INV[fidx]
                    # not INV(blocked[fidx]), but you don't know if it is blocked/unblocked
                    # INV(fact[fidx]), and then you don't need to try to push, because you already pushed
                    # but in this way you are actually pushing the cex/facts
                    

                    # synthesize a stronger one to push?
                    # variables?
                    # F[fidx - 2] /\ T --> INV[fidx - 1 ]
                    # not INV (blocked)
                    # INV(fact) /\ INV(fact[fidx])
                    # put in self.frames?
                    # try push this INV?
                    # threshold in construction ? grammar may be not enough?





    def is_last_two_frames_inductive(self):
        """Checks if last two frames are equivalent (no need to change variable to prime)"""
        if len(self.frames) > 1 and \
             self.solve(Not(Implies(And(self.frames[-1]), And(self.frames[-2]) ))) is None:
                return True
        return False

    def get_bad_state_from_property_invalid_after_trans(self, prop, idx, remove_vars = [], keep_vars = None):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        md, _ = self.solveTrans(self.frames[idx], \
            T = self.system.trans, prop = prop, \
            variables = self.system.variables, \
            remove_vars = remove_vars, keep_vars = keep_vars, findItp = False )
        return md


    def solve(self, formula, remove_vars = [], keep_vars = None):
        """Provides a satisfiable assignment to the state variables that are consistent with the input formula"""
        # you should know to drop variables here
        # plus tenary simulation ? ast-walker
        if self.solver.solve([formula]):
            retL = []
            for v, val in self.solver.get_model():
                if v in remove_vars:
                    continue
                if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v,val))
                #retL.append(EqualsOrIff(v, val))
            assert (len(retL) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return retL
        return None


    # you may want to have the interpolant here
    def solveTrans(self, prevF, T, prop , variables, remove_vars = [], keep_vars = None, findItp = False):
        # prevF /\ T(p, prime) --> not prop, if sat
        print (prevF + [T, Not( prop.substitute(self.prime_map))])
        if self.solver.solve( prevF + [T, Not( prop.substitute(self.prime_map))] ):
            model = self.solver.get_model()
            retL = []
            for v, val in model:
                if v not in variables: # if it is prime variable
                    continue # ignore it
                if v in remove_vars:
                    continue
                if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v,val))
            assert (len(retL) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return retL, None
        Itp = None
        if findItp:
            Itp = self.itp_solver.binary_interpolant( a = And(prevF + [T]), b= Not( prop.substitute(self.prime_map)) )
            Itp = And(Itp)
            Itp = Itp.substitute(self.primal_map)
            print ('get itp: ', str(Itp))
        return None, Itp



    # ---------------------------------------------------------------------------------


    def sanity_check_frame_monotone(self):
        assert (len(self.frames) > 1)
        for fidx in range(1,len(self.frames)):
            model = self.solve(Not(Implies(And(self.frames[fidx-1]), And(self.frames[fidx]))))
            if model is not None:
                self.dump_model(model)
                print ('Bug, not monotone, F%d -> F%d' % (fidx-1, fidx))
                assert (False)

    def dump_model(self, model):
        print (model)

    @staticmethod
    def print_cube(c):
        return ( '(' + ( ' && '.join([v.symbol_name() + ' = ' + str(val) for v, val in c]) ) + ')'  ) 


    # ---------------------------------------------------------------------------------
                
    def recursive_block(self, cube, idx, remove_vars = [], keep_vars = None):
        priorityQueue = []
        print ('recursive_block@F%d' % idx, self.print_cube(cube) )
        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve( \
                    And([self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]))
                assert (model_init_frame is not None)
                print ('CEX found!')
                return False

            prop = Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            model, itp = self.solveTrans(self.frames[fidx-1], \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )

            if model is None:
                self.frames[fidx].append(itp)
                if fidx not in self.cexs_blocked:
                    self.cexs_blocked[fidx] = []
                self.cexs_blocked[fidx].append(cex)
                heapq.heappop(priorityQueue) # pop this cex

            else:
                # model is not None
                heapq.heappush(priorityQueue, (fidx-1, cex))
        # TODO: 
        return True

        # for the CTG, see if we can block it or not?



def test_naive_pdr():
    width = 4
    cnt = BaseAddrCnt(width)
    prop = cnt.neq_property(1 << (width-1),1,1)
    pdr = PDR(cnt)
    pdr.check_property(prop)


if __name__ == '__main__':
    test_naive_pdr()