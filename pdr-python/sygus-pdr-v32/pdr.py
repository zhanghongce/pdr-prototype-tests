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
Config_debug_print = True
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
def debug(*l,**k):
    if Config_debug_print:
        print(*l, **k)


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
    def is_sat(self, prop):
        """returns True for valid property, prop : a single formula """
        if self.valid_solver.solve([prop]):
            return True
        return False
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
    def frame_implies(self, fidx, prop):
        if self.is_valid(Implies(self.frame_prop(fidx), prop)):
            return True
        return False
    def frame_compatible_w(self, fidx, prop):
        if self.is_sat(And(self.frame_prop_list(fidx) + [prop])):
            return True
        return False
            
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
    # *** END OF dump_frames ***

    
    #----------- TRANS - related  -------------------

    # you may want to have the interpolant here
    # used in recursive_block  and  get_bad_state_from_property_invalid_after_trans
    # use frame_prop_list for prevF !!!
    # --------------------------------------------------------------
    # NOTE:
    #       to be used as get_pre_post_state_from_property_invalid_after_trans:
    #       init = None, findItp = False, get_post_state = True
    def solveTrans(self, prevF, T, prop , variables, init, \
            remove_vars = [], keep_vars = None, findItp = False, get_post_state = False):
        assert (isinstance(prevF, list))
        # prevF /\ T(p, prime) --> not prop, if sat
        debug ('      [solveTrans] Property:', prop.serialize())
        debug ('      [solveTrans] var will => prime')
        #print ('      [solveTrans] prevF:', prevF)
        debug ('      [solveTrans] use Init:', init is not None)

        if init is None:
            f = prevF + [T, Not( prop.substitute(self.prime_map))]
        else:
            f = [Or(And(prevF+[T]), init.substitute(self.prime_map) ) , Not( prop.substitute(self.prime_map))]
        #print (f)
        if self.solver.solve(f):
            model = self.solver.get_model()
            pre_ex = [], post_ex = []
            for v, val in model:
                if v in variables:
                    # pre_ex
                    if v in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v not in keep_vars:
                        continue
                    pre_ex.append((v,val))
                elif get_post_state:
                    v_primal = self.primal_map[v]
                    if v_primal in remove_vars:
                        continue
                    if isinstance(keep_vars, list) and len(keep_vars) > 0 and v_primal not in keep_vars:
                        continue
                    post_ex.append((v_primal,val))
            assert (len(pre_ex) > 0) # otherwise we are removing too many variables!
            #return And(retL)
            return pre_ex, post_ex, None
        Itp = None
        if findItp:
            if init is None:
                a = And(prevF + [T])
                b = Not( prop.substitute(self.prime_map))
            else:
                a = f[0]
                b = f[1]
            Itp = self.itp_solver.binary_interpolant( a = a, b = b)
            Itp = And(Itp)
            Itp = Itp.substitute(self.primal_map)
            if Config_simplify_itp:
                Itp = simplify(Itp)
            debug ('    [solveTrans] get itp: ', Itp.serialize())
            #pause()
        return None, None, Itp
    # *** END OF solveTrans ***

    # used in check_property, check_init_failed
    # not in push_lemma, because we also want the pre-&post-states
    def get_bad_state_from_property_invalid_after_trans(self, prop, idx, use_init, remove_vars = [], keep_vars = None):
        """Extracts a reachable state that intersects the negation
        of the property and the last current frame"""
        assert (idx >= 0)
        print ('    [F%d -> prop]' % idx)
        md, _ , _ = self.solveTrans(self.frame_prop_list(idx), \
            T = self.system.trans, prop = prop, \
            init = self.system.init if use_init else None,
            variables = self.system.variables, \
            remove_vars = remove_vars, keep_vars = keep_vars, findItp = True, get_post_state=False )
        # no need for itp here
        #pause()
        return md
    # *** END OF get_bad_state_from_property_invalid_after_trans ***

    def do_recursive_block(self, cube, idx, cex_origin, remove_vars = [], keep_vars = None ):
        assert isinstance(cex_origin, tuple )
        cex_push_origin = cex_origin[0]
        cex_create_origin = cex_origin[1]

        priorityQueue = []
        print ('      [block] Try @F%d' % idx, self.print_cube(cube) )

        prop = _cube2prop(cube)
        if self.frame_implies(idx, prop):
            print ('      [block] already blocked by F%d' % idx)
            return True

        heapq.heappush(priorityQueue, (idx, cube))
        while len(priorityQueue) > 0:
            fidx, cex = heapq.nsmallest(1, priorityQueue)[0]

            if fidx == 0:
                model_init_frame = self.solve( \
                    [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex])
                assert (model_init_frame is not None)
                print ('      [block] CEX found!')
                return False

            prop = Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('      [block] check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            #if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        print ('      [block] CEX is reachable -- direct init!')
            #        return False
            
            model, itp = self.solveTrans(self.frames[fidx-1] + ([prop] if Config_rm_cex_in_prev else []), \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                init = self.system.init, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True )

            if model is None:
                if cex_push_origin is not None:
                  new_cex_push_origin = cex_push_origin if idx == fidx else None
                else:
                  new_cex_push_origin = None

                cidx = self._add_cex(fidx = fidx, cex = cex, origin = (new_cex_push_origin, cex_create_origin))

                self._add_lemma(lemma = itp, fidx = fidx, cidxs = {cidx} )
                if not self.is_valid( Implies(And(self.frames[fidx-1]), itp) ):
                    self._add_lemma_to_all_prev_frame( end_frame_id = fidx-1, lemma = itp )
                    print ('    [block] add ITP to F1 ->>- F%d: ' % (fidx-1), itp.serialize())
                    # add cex to all previous ones and this will block it 
                    # or, maybe you don't need it because it is already pushed before the current frame
                    # and should not interfere with the not yet pushed lemma.

                heapq.heappop(priorityQueue) # pop this cex

            else:
                # model is not None
                print ('      [block] push to queue, F%d' % (fidx-1), self.print_cube(model))
                heapq.heappush(priorityQueue, (fidx-1, model))
        # TODO: 
        print ('      [block] Succeed, return.')
        return True
    # *** END OF do_recursive_block ***
