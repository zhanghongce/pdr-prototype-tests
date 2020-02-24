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
    def direct_push(self): # -> Lemma:
        self.pushed = True
        ret = Lemma(expr = self.expr, cex = self.cex, origin = self.origin)
        ret.itp_push_failed = (self.itp_push_failed[0] , self.itp_push_failed[0]+1)
        ret.itp_enhance_fail = self.itp_enhance_fail
        return ret
    # think about repairing
    # think about contracting
    # think about itp change form
    def serialize(self):
        return self.expr.serialize()
# *** END OF Lemma ***

class FrameCache(object):
    def __init__(self):
        self.frames = {} # idx -> list of lemmas
    def _add_lemma(self, lemma, fidx):
        # TODO:
        pass
    def _add_pushed_lemma(self, lemma, start, end):
        # TODO:
        pass
    def frame_prop_list(self, fidx):
        assert fidx in self.frames
        return [l.expr for l in self.frames[fidx]]
    def copy(self):
        # TODO: 
        pass
    # insert a frame to this one ???
# *** END OF FrameCache ***
    


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
    def frame_not_implies_model(self, fidx, prop):
        return self.get_not_valid_model(Implies(self.frame_prop(fidx), prop))

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

    #----------- FRAME HANDLing  -------------------

    def _add_lemma(self, lemma, fidx):
        # TODO
        pass

    def _add_pushed_lemma(self, lemma, start, end):
        # TODO
        pass
    
    def _add_fact(self,fact, fidx):
        #TODO:
        pass
    
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
        assert isinstance(cex_origin, str )

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

            prop = _cube2prop(cex) #Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('      [block] check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            #if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        print ('      [block] CEX is reachable -- direct init!')
            #        return False
            
            model, _, itp = self.solveTrans(self.frame_prop_list(fidx-1) + ([prop] if Config_rm_cex_in_prev else []), \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                init = self.system.init, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True, get_post_state=False )

            if model is None:
                lemma = Lemma(expr=itp, cex={cex}, origin=cex_origin)
                self._add_lemma(lemma = lemma, fidx = fidx)
                self._add_pushed_lemma(lemma = lemma, start = 1, end = fidx -1 )
                heapq.heappop(priorityQueue) # pop this cex
            else:
                # model is not None
                print ('      [block] push to queue, F%d' % (fidx-1), self.print_cube(model))
                heapq.heappush(priorityQueue, (fidx-1, model))
        print ('      [block] Succeed, return.')
        return True
    # *** END OF do_recursive_block ***

    def try_recursive_block(self, cube, idx, cex_origin, frame_cache: FrameCache,  remove_vars = [], keep_vars = None ):
        assert isinstance(cex_origin, str )

        priorityQueue = []
        print ('      [block] Try @F%d' % idx, self.print_cube(cube) )

        prop = _cube2prop(cube)

        if self.is_valid(Implies(And(self.frame_prop_list(idx) + frame_cache.frame_prop_list(idx)), prop)):
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

            prop = _cube2prop(cex) #Not(And([EqualsOrIff(v,val) for v,val in cex]))
            
            # Question: too old itp? useful or not?
            # push on older frames also? for new ITP?
            print ('      [block] check at F%d -> F%d : ' % (fidx-1, fidx), str(prop)  )
            #if Config_rm_cex_in_prev:
            #    if (self.solve( \
            #            [self.system.init] +  [EqualsOrIff(v,val) for v,val in cex]) is not None):
            #        print ('      [block] CEX is reachable -- direct init!')
            #        return False
            
            model, _, itp = self.solveTrans(
                self.frame_prop_list(fidx-1) \
                     + frame_cache.frame_prop_list(fidx-1) \
                     + ([prop] if Config_rm_cex_in_prev else []), \
                T = self.system.trans, prop = prop, \
                variables = self.system.variables, \
                init = self.system.init, \
                remove_vars = remove_vars, keep_vars = keep_vars, findItp = True, get_post_state=False )

            if model is None:
                lemma = Lemma(expr=itp, cex={cex}, origin=cex_origin)
                frame_cache._add_lemma(lemma = lemma, fidx = fidx)
                frame_cache._add_pushed_lemma(lemma = lemma, start = 1, end = fidx -1 )
                heapq.heappop(priorityQueue) # pop this cex
            else:
                # model is not None
                print ('      [block] push to queue, F%d' % (fidx-1), self.print_cube(model))
                heapq.heappush(priorityQueue, (fidx-1, model))
        print ('      [block] Succeed, return.')
        return True
    # *** END OF try_recursive_block ***

    #----------- PROCEDURES -------------------

    def check_init_failed(self, prop, remove_vars, keep_vars):
        init_cex = self.frame_not_implies_model(fidx=0,prop=prop)
        print ("[Checking init] F0 and not P")
        if init_cex is not None:
            print("[Checking init] Property failed at INIT")
            print("[Checking init] CEX: ", self.print_cube(init_cex))
            return True
        print ("[Checking init]  F0 and T and not P'")
        init_cex = self.get_bad_state_from_property_invalid_after_trans(
            prop = prop, idx = 0, use_init = True, remove_vars = remove_vars, keep_vars = keep_vars)
        if init_cex is not None:
            print("[Checking init] Property failed at F1")
            print("[Checking init] CEX @F0: ", self.print_cube(init_cex))
            return True
        print ("[Checking init] Done")
        return False
    # *** END OF check_init_failed ***

    def check_property(self, prop, remove_vars = [], keep_vars = None):
        """Property Directed Reachability approach without optimizations."""
        print("[Checking property] Property: %s." % prop)

        if self.check_init_failed(prop, remove_vars, keep_vars):
            return False

        # self._add_lemma(fidx = 1, lemma = prop) : no need
        # its interpolant may be too small

        while True:
            self.sanity_check_frame_monotone()
            self.sanity_check_imply()
            self.dump_frames()
            print ('Total Frames: %d, L %d ' %( len(self.frames) , len(self.frames[-1])))
            pause ()

            # frame[-1] /\ T -> not (prop)
            cube = self.get_bad_state_from_property_invalid_after_trans( \
                prop = prop, idx = len(self.frames)-1, use_init = False, remove_vars = remove_vars, keep_vars = keep_vars)

            print ('[Checking property] Get cube: ', cube , ' @F%d' % (len(self.frames)-1))
            # cube is list of (var, assignments)
            if cube is not None:
                # Blocking phase of a bad state
                if not self.do_recursive_block(cube, len(self.frames)-1, cex_origin = 'prop', remove_vars = remove_vars, keep_vars=keep_vars ):
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
                    self.push_lemma_from_the_lowest_frame(remove_vars, keep_vars)
                    if self.is_last_two_frames_inductive():
                        print("[Checking property] The system is safe, frame : %d" % len(self.frames) )
                        return True
    # *** END OF check_property ***

    # put too few in the      
    def push_lemma_from_the_lowest_frame(self, remove_vars, keep_vars):
        start_frame = 1 # let's try not to worry about caching this at this time
        # do not push from the initial frame
        print ('[pushes] F%d --- F%d' % (start_frame, len(self.frames)-2))
        for fidx in range(start_frame, len(self.frames)-1):
            self.push_lemma_from_frame(fidx, remove_vars, keep_vars)
    # *** END OF push_lemma_from_the_lowest_frame ***

    #----------- !!! PUSH LEMMA !!! -------------------

    def push_lemma_from_frame(self, fidx, remove_vars, keep_vars):
        assert (len(self.frames) > fidx+1)
        assert (len(self.frames[fidx]) > 0 )

        # 1. push facts
        start_fact_idx = self.facts_pushed_idxs_map.get(fidx, 0)
        end_fact_idx = len(self.unblockable_fact[fidx])
        if fidx in self.unblockable_fact:
            for factIdx in range(start_fact_idx, end_fact_idx):
                fact = self.unblockable_fact[fidx][factIdx]
                # once a fact always a fact
                if fact not in self.unblockable_fact.get(fidx+1,[]):
                    self._add_fact(fact = fact, fidx = fidx + 1)
        self.facts_pushed_idxs_map[fidx] = end_fact_idx
                
        ## push lemmas
        start_lemma_idx = self.frames_pushed_idxs_map.get(fidx, 0)
        end_lemma_idx   = len(self.frames[fidx])

        unpushed_lemmas = [] # list of (lidx, lemma, prev_ex, post_ex )

        # 1. try direct push
        for lemmaIdx in range(start_lemma_idx, end_lemma_idx):
            lemma : Lemma = self.frames[fidx][lemmaIdx]
            if lemma.pushed:
                continue
            print ('  [push_lemma F%d] Try pushing lemma l%d to F%d: ' % (fidx, lemmaIdx, fidx+1) , (lemma.serialize()))

            prev_ex, post_ex, _ = \
                self.solveTrans(prevF=self.frame_prop_list(fidx), 
                T=self.system.trans,prop=lemma,variables=self.system.variables, 
                init=None,remove_vars=remove_vars, keep_vars=keep_vars, 
                findItp=False,get_post_state=True)
            # variables there is to distinguish vars and prime vars

            if prev_ex is None: # post_ex should be none also
                # push is successful
                assert (post_ex is None)
                print ('  [push_lemma F%d] Succeed in pushing l%d!'%(fidx, lemmaIdx))
                self._add_lemma(lemma.direct_push(), fidx = fidx+1) # together with its cex
            else: # there is a failing model
                # store if temporarily and we will decide how to deal with them
                unpushed_lemmas.append((lemmaIdx, lemma, prev_ex, post_ex))
        # finish pushing all that can be pushed  
        # start to deal with unpushed

        # 2. handled unpushed lemmas
        for lemmaIdx, lemma, prev_ex, post_ex in unpushed_lemmas:
            if len(lemma.cex) == 0:
                print ('  [push_lemma F%d] will give up on lemma as it blocks None, '%(fidx), 'l'+str(lemmaIdx)+':',  lemma.serialize())
                continue
            # 2.1 if subsume, then we don't need to worry about
            if lemma.subsume_by_next_frame():
                continue
            # 2.2 try itp repair
            itp_fc = FrameCache() # self as an fc also, but the solver etc also
            cex_failed , itp = lemma.try_itp_push(itp_fc) # itp is also in the framecache
            # itp is a Lemma
            if cex_failed:
                assert (itp is None)
                # not pushable 
                print ('  [push_lemma F%d] skip r-block l%d :'%(fidx, lemmaIdx) , lemma.serialize(), ' as its cex cannot be pushed.')
                continue

            # 2.3 sygus repair
            sygus_hint:Lemma = self._try_sygus_repair(lemma)
            if sygus_hint is not None:
                # succeed in repair
                self._add_lemma(lemma = sygus_hint, fidx = fidx+1)
                self._add_pushed_lemma(lemma = sygus_hint, start = 1, end = fidx)
                print ('  [push_lemma F%d] repair l%d :'%(fidx, lemmaIdx) , lemma.serialize())
                print ('  [push_lemma F%d] get l%d :'%(fidx, lemmaIdx) , sygus_hint.serialize())
                continue

            # 2.4 try contraction 
            strengthen_fc = FrameCache() # self as an fc also, but the solver etc also
            prop_succ, all_succ, time_out, unblockable_cube = lemma.try_strengthen(strengthen_fc, bound)
            # full/prop itself/bad_state
            if all_succ or prop_succ:
                print ('  [push_lemma F%d] strengthened l%d :'%(fidx, lemmaIdx) , lemma.serialize(), " with extra lemma")
                self.merge_frame_cache(strengthen_fc)
                continue

            if unblockable_cube is not None:
                assert (not time_out)
                self._add_fact(fact = unblockable_cube, fidx = fidx)

            print ('  [push_lemma F%d] unable to push l%d :'%(fidx, lemmaIdx) , lemma.serialize())
            print ('  [push_lemma F%d] use new itp l%d :'%(fidx, lemmaIdx), itp.serialize())
                



            

                

            # get its recursive blocked
            # try itp push : given a framcecache?
            # try recurisve push : given a framecache?
            # try sygus push

        # F. update pushed
        self.frames_pushed_idxs_map[fidx] = end_lemma_idx

    # *** END OF push_lemma_from_frame ***