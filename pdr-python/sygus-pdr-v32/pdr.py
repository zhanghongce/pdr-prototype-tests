from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV, EqualsOrIff, BVNot, BVSub
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from pysmt.shortcuts import Interpolator, simplify
from pysmt.logics import QF_BV
# Type annotation
from typing import Sequence, Callable

from utilfunc import _get_var, _get_cubes_with_more_var, _get_cubes_with_fewer_var
from cegpbe import CexGuidedPBE
from opextract import OpExtractor
from sts import TransitionSystem, BaseAddrCnt, TwoCnt, TwoCntNoload

import heapq


#----------- Basic Parameters -------------------
Config_Max_Frame = 10000000
Config_use_itp_in_pushing = False
Config_analyze_use_itp_in_pushing = True
Config_debug = True
Config_simplify_itp = True
Config_rm_cex_in_prev = True
#----------- Heuristics -------------------
Config_enhance_giveup_threshold = (2, 3) # (8,10)
Config_cex_invalid_itp_guess_threshold = (4,5) # (18, 20)
Config_try_drop_cex = (5,5) # (30, 50)  # after 30 frames, per 50
#----------- NEEDS EXPERIMENTS -------------------
Config_use_fact_in_sygus = False
Config_strengthen_effort_for_prop = 1e10 # almost infinity (should make it 1000?)


def pause():
    if Config_debug:
        input()


#----------- AUX FUNCTIONS -------------------
def _cube2prop(cube):
  return Not(And([EqualsOrIff(v,val) for v,val in cube]))



#----------- AUX CLASSES -------------------

class Lemma(object):
    @classmethod
    def _canonicalize_cex(cls, cex):
        """cex to a hashable thing"""
        cex_str = [(v.symbol_name(), val) for v, val in cex ]
        return tuple(sorted(cex_str, key = lambda x: x[0]))

    def __init__(self, expr, cex, origin):
        # cex should be a set
        assert (isinstance(cex, set))
        self.expr = expr
        self.cex  = cex
        self.origin = origin
        self.pushed = False
        # statistics
        self.itp_push_failed = (0,0)
        self.itp_enhance_fail = (0,0)
    def push(self): # -> Lemma:
        self.pushed = True
        ret = Lemma(expr = self.expr, cex = self.cex, origin = self.origin)
        ret.itp_push_failed = (self.itp_push_failed[0] , self.itp_push_failed[0]+1)
        ret.itp_enhance_fail = self.itp_enhance_fail
        return ret
    # think about repairing
    # think about contracting
    # think about itp change form



#----------- MAIN CLASS -------------------

class PDR(object):
    def __init__(self, system):
        self.system = system
        init_lemma = Lemma(expr = system.init, cex = set(), origin = 'init')
        self.frames = [ [init_lemma], []  ] # list of list of clauses

        self.prime_map = dict([(v, TransitionSystem.get_prime(v)) for v in self.system.variables])
        self.primal_map = dict([(TransitionSystem.get_prime(v), v) for v in self.system.variables])
        
        self.solver = Solver(name = 'z3') # use z3 for partial model
        self.valid_solver = self.solver # we can use btor later 
        self.itp_solver = Interpolator(logic=QF_BV)

        self.unblockable_fact = {} # <n, ex> : n -> list of ex, unblocked, used to syn

        self.frames_pushed_idxs_map = {} # n->idx+1 tried
        self.facts_pushed_idxs_map = {} # n->idx+1 tried


    #----------- SOLVING PRIMITIVES -------------------
    def is_valid(self, prop):
        """returns True for valid property, prop : a single formula """
        if self.valid_solver.solve([Not(prop)]):
            return False
        return True
    # *** END OF is_valid ***
    def get_not_valid_model(self, prop):
        if self.valid_solver.solve([Not(prop)]):
            return self.valid_solver.get_model()
        return None
    # *** END OF get_not_valid_model ***

    def solve(self, formula, remove_vars = [], keep_vars = None):
        """Provides a satisfiable assignment to the state 
        variables that are consistent with the input formula,
        formula : property or a list of property
        returns : a cube : [(v,val)]"""
        # you should know to drop variables here
        # plus tenary simulation ? ast-walker
        if not isinstance(formula, list):
            formula = [formula]
        if self.solver.solve(formula):
            retL = []
            for v, val in self.solver.get_model():
                if v in remove_vars:
                    continue
                if (isinstance(keep_vars, list) or isinstance(keep_vars, set) ) and len(keep_vars) > 0 and v not in keep_vars:
                    continue
                retL.append((v,val))
                #retL.append(EqualsOrIff(v, val))
            assert (len(retL) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return retL
        return None
    # *** END OF solve ***

    #----------- FRAME to Properties -------------------
    def frame_prop_list(self, fidx):
        return [l.expr for l in self.frames[fidx]]
    def frame_prop(self, fidx): # all prop
        return And([l.expr for l in self.frames[fidx]])
    def frame_prop_select(self, fidx, selector : Callable[[int],bool]): # which to keep
        return And([l.expr for lidx,l in enumerate(self.frames[fidx]) if  selector(lidx) ])
    def get_inv(self):
        return self.frame_prop(fidx = -1)
            
    #----------- FRAME Checks -------------------
    def is_last_two_frames_inductive(self):
        """Checks if last two frames are equivalent (no need to change variable to prime)"""
        if len(self.frames) > 1 and \
             self.is_valid( Implies(self.frame_prop(fidx = -1), self.frame_prop(fidx = -2)) ):
                return True
        return False
        
    def sanity_check_safe_inductive_inv(self, prop ):
        T = self.system.trans
        inv = self.get_inv()
        inv_prime = inv.substitute(self.prime_map)
        assert ( self.is_valid(Implies(self.system.init,inv)))
        assert ( self.is_valid(Implies(And(inv, T), inv_prime)))
        assert ( self.is_valid(Implies(inv, prop)))

    def sanity_check_imply(self):
        assert (len(self.frames) > 1)
        T = self.system.trans
        for fidx in range(1,len(self.frames)):
            next_frame = self.frame_prop(fidx = fidx)
            next_frame = next_frame.substitute(self.prime_map)
            assert ( self.is_valid(Implies(And(self.frame_prop(fidx-1) ,T), next_frame)) )
            #if model is not None:
            #    print ('Bug, F%d and T -/-> F%d' % (fidx-1, fidx))
            #    assert (False)

    def sanity_check_frame_monotone(self):
        assert (len(self.frames) > 1)
        for fidx in range(1,len(self.frames)):
            valid = self.is_valid(Implies(self.frame_prop(fidx-1), self.frame_prop(fidx)))
            if not valid:
                self.dump_frames()
                print ('Bug, not monotone, F%d -> F%d' % (fidx-1, fidx))

                print ('Bug lemmas in F%d' % fidx)
                for lemmaIdx, lemma in enumerate(self.frame_prop_list(fidx)):
                    model = self.get_not_valid_model(Implies(self.frame_prop(fidx-1), lemma))
                    if model is not None:
                        print (' l%d : ' % lemmaIdx, lemma.serialize())
                assert (False)

    #----------- PRINTINGs -------------------

    @staticmethod
    def print_cube(c):
        return ( '(' + ( ' && '.join([v.symbol_name() + ' = ' + str(val) for v, val in c]) ) + ')'  ) 
    def dump_frames(self, toStr = False):
        retS = []
        def _printStr(*argl, **argd):
            if (toStr):
                retS.append( ''.join ( argl ) )
            else:
                print(*argl, **argd)
        _printStr ('---------- Frames DUMP ----------')
        #  TODO: 
        _printStr ('---------- END Frames DUMP ----------')
        return '\n'.join(retS)