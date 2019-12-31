from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV, EqualsOrIff, BVNot, BVSub
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.shortcuts import Interpolator
from pysmt.logics import QF_BV

from sygus import ItpEnhance

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

Config_Max_Frame = 10000000


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


class TwoCnt(TransitionSystem):
    def __init__(self, nbits, zero_init = False):
        self.nbits = nbits # save the number of bits
        self.mask = 2**(nbits)-1

        self.c1   = Symbol('c1', BVType(nbits))
        self.c2   = Symbol('c2', BVType(nbits))
        self.inp  = Symbol('inp',  BVType(nbits))
        self.lden = Symbol('lden',  BVType(1))

        variables = [self.c1, self.c2, self.inp, self.lden]
        prime_variables = [next_var(v) for v in variables]
        if zero_init:
            init = self.c1.Equals(0) & self.c2.Equals(self.mask)
        else:
            init = self.c1.Equals(self.inp) & self.c2.Equals(BVNot(self.inp))
        trans= next_var(self.c1).Equals( \
            Ite(self.lden.Equals(1), self.inp, BVAdd(self.c1, BV(1, nbits)  ))) & \
            next_var(self.c2).Equals( \
            Ite(self.lden.Equals(1), BVNot(self.inp), BVSub(self.c2, BV(1, nbits)  )))
            
        TransitionSystem.__init__(self, \
          variables = variables, \
          prime_variables = prime_variables, \
          init = init, trans = trans )

    def neq_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 != self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )

    def false_property(self, c1, c2):
        c1 = c1 & self.mask
        c2 = c2 & self.mask

        assert ( c1 + c2 == self.mask)

        return Not( self.c1.Equals(c1) & self.c2.Equals(c2) )



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


        self.cexs_pushed_idxs_map = {} # n->idx+1 tried
        self.frames_pushed_idxs_map = {} # n->idx+1 tried
        self.min_cex_frames_changed = Config_Max_Frame
        # map: v --> next_v

    def dump_frames(self):
        print ('---------- Frames DUMP ----------')
        for fidx,f in enumerate(self.frames):
            print ('Frame : %d'%fidx)
            for lidx, lemma in enumerate(f):
                ptr = '*' if self.frames_pushed_idxs_map.get(fidx,0) == lidx else ' '
                print ('  %s l%d: ' % (ptr,lidx) , lemma.serialize())
            if self.frames_pushed_idxs_map.get(fidx,0) == lidx + 1:
                print ('    all tried to push')

            if fidx in self.cexs_blocked:
                print ('  CEX blocked # : %d'% len(self.cexs_blocked[fidx]) )
                for cidx, cex in enumerate(self.cexs_blocked[fidx]):
                    ptr = '*' if self.cexs_pushed_idxs_map.get(fidx,0) == cidx else ' '
                    print ('  %s c%d: ' % (ptr, cidx), self.print_cube(cex) )
                if self.cexs_pushed_idxs_map.get(fidx,0) == lidx + 1:
                    print ('    all tried to push')
            if fidx in self.unblockable_fact:
                print ('  facts # : %d'% len(self.unblockable_fact[fidx]) )
                for cidx, fact in enumerate(self.unblockable_fact[fidx]):
                    print ('    f%d: ' % cidx, self.print_cube(fact) )
        print ('---------- END Frames DUMP ----------')


    def check_init_failed(self, prop, remove_vars, keep_vars):
        init_cex = self.solve(And(self.frames[0] + [ Not(prop) ] ))
        if init_cex is not None:
            print("[Checking property] Property failed at INIT")
            print("[Checking property] CEX: ", self.print_cube(init_cex))
            return True
        init_cex = self.get_bad_state_from_property_invalid_after_trans(prop, 0, remove_vars, keep_vars )
        if init_cex is not None:
            print("[Checking property] Property failed at F1")
            print("[Checking property] CEX @F0: ", self.print_cube(init_cex))
            return True
        return False



    def check_property(self, prop, remove_vars = [], keep_vars = None):
        """Property Directed Reachability approach without optimizations."""
        print("[Checking property] Property: %s." % prop)

        if self.check_init_failed(prop, remove_vars, keep_vars):
            return False

        while True:
            self.sanity_check_frame_monotone()
            self.dump_frames()

            # frame[-1] /\ T -> not (prop)
            cube = self.get_bad_state_from_property_invalid_after_trans(prop, -1, remove_vars, keep_vars)

            print ('[Checking property] Get cube: ', cube , ' @F%d' % (len(self.frames)-1))
            # cube is list of (var, assignments)
            if cube is not None:
                # Blocking phase of a bad state
                if not self.recursive_block(cube, len(self.frames)-1, remove_vars, keep_vars ):
                    print("[Checking property] Bug found at step %d" % (len(self.frames)))
                    return False
                else:
                    print("[Checking property] Cube blocked '%s'" % self.print_cube(cube))
            else:
                # Checking if the last two frames are equivalent i.e., are inductive
                if self.is_last_two_frames_inductive():
                    print("[Checking property] The system is safe, frame : %d" % len(self.frames) )
                    return True
                else:
                    print("[Checking property] Adding frame %d..." % (len(self.frames)))
                    self.frames.append([])
                    self.push_lemma_from_the_lowest_frame(remove_vars, keep_vars) # TODO
                    # you should try to push existing clauses
    
    # TODO: problem : INIT -> next frame ????
    # put too few in the      
    def push_lemma_from_the_lowest_frame(self, remove_vars, keep_vars):
        if self.min_cex_frames_changed == Config_Max_Frame:
            self.min_cex_frames_changed = 1
        start_frame = self.min_cex_frames_changed
        # do not push from the initial frame
        print ('[pushes] F%d to F%d' % (start_frame, len(self.frames)-2))
        self.min_cex_frames_changed = len(self.frames)-1
        for fidx in range(start_frame, len(self.frames)-1):
            self.push_lemma_from_frame(fidx, remove_vars, keep_vars)


    def push_lemma_from_frame(self, fidx, remove_vars, keep_vars):
        assert (len(self.frames) > fidx+1)
        if (fidx not in self.cexs_blocked): # else no cex to push
            print ('  [push_lemma from F%d] <WARN> no cex to push from F%d'%(fidx,fidx))
            input ()
        assert (fidx in self.cexs_blocked)
        
        start_cexs_idx = self.cexs_pushed_idxs_map.get(fidx,0)
        end_cex_idx    = len(self.cexs_blocked[fidx])

        for cexIdx in range(start_cexs_idx,end_cex_idx):
            cex = self.cexs_blocked[fidx][cexIdx]
            print ('  [push_lemma F%d] cex to try: c%d :'%(fidx, cexIdx), self.print_cube(cex))
            if self.recursive_block(cex, fidx+1, remove_vars, keep_vars):
                print ('  [push_lemma F%d] cex is pushed: '%fidx, self.print_cube(cex))
        self.cexs_pushed_idxs_map[fidx] =  end_cex_idx # we will push all the cexs at the early time

        # if len(self.cexs_blocked[fidx]) > end_cex_idx: there are now more cexs to try pushing
        # there could be more cexs to push (we can decide if we want to add a loop here)

        start_lemma_idx = self.frames_pushed_idxs_map.get(fidx, 0)
        end_lemma_idx   = len(self.frames[fidx]) # we can decide if we want to update this
        lemmaIdx = start_lemma_idx
        while lemmaIdx != end_lemma_idx:
            lemma = self.frames[fidx][lemmaIdx]
            print ('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx+1) , (lemma.serialize()))
            ex = self.get_bad_state_from_property_invalid_after_trans(lemma, fidx, remove_vars, keep_vars )

            if ex is None: # no bad state, lemma is still valid
                self.frames[fidx+1].append(lemma)
                self.min_cex_frames_changed = min(fidx+1,self.min_cex_frames_changed)
                print ('  [push_lemma F%d] Succeed in pushing!'%fidx)
                lemmaIdx += 1 # try next one
            else:
                print ('  [push_lemma F%d] find cex@F%d : %s' % (fidx, fidx, self.print_cube(ex)))
                if self.recursive_block(ex, fidx, remove_vars, keep_vars ):
                    #lemmas_to_try.append(lemma)
                    continue # retry in the next round
                    # if blocked so what? retry
                else:
                    if fidx not in self.unblockable_fact:
                        self.unblockable_fact[fidx] = []
                    self.unblockable_fact[fidx].append(ex)
                    print ('  [push_lemma F%d] fail due to fact'%fidx , self.print_cube(ex))
                    lemmaIdx+= 1

                    self.dump_frames()
                    print ('  [push_lemma F%d] Should invoke SyGuS here ... ' % fidx)
                    input()

            # end_lemma_idx = len(self.frames) # should we do this or not?

        self.frames_pushed_idxs_map[fidx] =  end_lemma_idx
        # if len(self.frames[fidx]) > end_lemma_idx : we have unpushed lemmas
        # how hard to try?
        print ('  [push_lemma F%d] push lemma finished, press any key to continue'%fidx)
        input()

        # try new lemmas ? 

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
        print ('    [F%d -> prop]' % idx)
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
        print ('      [solveTrans] Property:', prop.serialize())
        print ('      [solveTrans] var will => prime')
        print ('      [solveTrans] prevF:', prevF)

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
            print ('    [solveTrans] get itp: ', Itp.serialize())
            input()
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
        print ('      [block] Try @F%d' % idx, self.print_cube(cube) )
        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve( \
                    And([self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]))
                assert (model_init_frame is not None)
                print ('      [block] CEX found!')
                return False

            prop = Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('      [block] check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            model, itp = self.solveTrans(self.frames[fidx-1], \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )

            if model is None:
                self.frames[fidx].append(itp)
                if fidx not in self.cexs_blocked:
                    self.cexs_blocked[fidx] = []
                self.min_cex_frames_changed = min(self.min_cex_frames_changed, fidx)

                self.cexs_blocked[fidx].append(cex)
                heapq.heappop(priorityQueue) # pop this cex

            else:
                # model is not None
                print ('      [block] push to queue, F%d' % (fidx-1), self.print_cube(model))
                heapq.heappush(priorityQueue, (fidx-1, model))
        # TODO: 
        print ('      [block] Succeed, return.')
        return True

        # for the CTG, see if we can block it or not?


def test_naive_pdr():
    width = 4
    cnt = BaseAddrCnt(width)
    prop = cnt.neq_property(1 << (width-1),1,1)
    pdr = PDR(cnt)
    pdr.check_property(prop)


def test_naive_pdr_2cnt():
    width = 4
    cnt = TwoCnt(width, True)
    prop = cnt.false_property(7,8)
    pdr = PDR(cnt)
    pdr.check_property(prop)

if __name__ == '__main__':
    test_naive_pdr_2cnt()
