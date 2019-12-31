from pysmt.shortcuts import Symbol, Not, And, Or, Implies, Ite, BVAdd, BV
from pysmt.shortcuts import is_sat, is_unsat, Solver, TRUE
from pysmt.typing import BOOL, BVType
from opextract import OpExtractor


Config_expand_values = False
Config_use_trans = True
Config_use_facts = True
Config_smtlib2_daggify = True

# get the variable of ex
# get the operators of lemma
# get the unblockable fact of these variables
#    and all other with more variables, 
# get the cexs of these variables or fewer
# sygus  --- what if there are conflicts??? (should not be)
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

def _get_var(c):
  return set([v for v, _ in c])

def _get_cubes_with_fewer_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issubset(vset)]

def _get_cubes_with_more_var(cubes, vset):
  # sort based on variable
  return [dict(cube) for cube in cubes if _get_var(cube).issuperset(vset)]

def _sanity_check_no_conflict(facts, blocked, vset):
  solver = Solver()
  for cube in facts:
    # facts with more vars
    solver.add_assertion(And([EqualsOrIff(v,val) for v,val in cube if v in vset]))

  for cube in blocked:
    solver.add_assertion(Not(And([EqualsOrIff(v,val) for v,val in cube if v in vset])))

  assert ( solver.solve() ) # we expect it is satisfiable

def _get_unified_width(v): # bool 0, bv ... 
  if v.get_type().is_bool_type():
    return 0
  assert (v.get_type().is_bv_type())
  return v.bv_width()

def _to_type_string(v):
  if v.get_type().is_bool_type():
    return 'Bool'
  assert (v.get_type().is_bv_type())
  return ('(_ BitVec %d)' % v.bv_width())

def _to_name_type(v): # v should be a pysmt v
  assert (v.is_symbol())
  return '('+v.symbol_name() + " " + _to_type_string(v)+')'

def _to_name_type_suffix_no_p(v, suffix): # v should be a pysmt v
  assert (v.is_symbol())
  return v.symbol_name() + suffix + " " + _to_type_string(v)

def _to_args(vl):
  return '('+ (' '.join([_to_name_type(v) for v in vl])) + ')'

def _to_tr_args(vl, vp):
  return '('+ (' '.join([_to_name_type(v) for v in vl] + [_to_name_type(v) for v in vp])) + ')'

def _const_to_str(fn):
  if fn.is_bv_constant():
    return '#b' + fn.bv_str()
  elif fn.is_bool_constant():
    return 'true' if fn.is_true() else 'false'
  assert (False) # unknown type

def _gen_define_extracts(inw, h, l, outw):
  assert (h >= l)
  assert (h < inw)
  assert (l >= 0)
  assert (h-l +1 == outw)
  assert (outw > 0)
  k = 'extractH%dL%dF%dT%d' % (h, l, inw, outw)
  retStr = ( '(define-fun '+k)
  retStr += (' ((in %s)) ' % BvConstructs.width_to_type(inw) ) + BvConstructs.width_to_type(outw) + \
    (' ((_ extract %d %d) in)' % (h,l))
  retStr += ')'
  repls = '(_ extract %d %d)' % (h,l)
  return k, retStr, repls


def _gen_define_rotate(op, param, outw): # inw = outw
  assert (outw > 0)
  assert (param > 0)
  k = '%sP%dT%d' % (op, param, outw)
  retStr = ( '(define-fun ' + k)

  if op == 'rol':
    smt_op = 'rotate_left'
  elif op == 'ror':
    smt_op = 'rotate_right'
  else:
    assert False

  retStr += (' ((in %s)) ' % BvConstructs.width_to_type(outw) ) + BvConstructs.width_to_type(outw) + \
    ' ((_ %s %d) in)' % (smt_op, param)
  retStr += ')'
  repls = '(_ %s %d)' % (smt_op, param)
  return k, retStr, repls

def _gen_define_extend(op, param, inw, outw ): # inw = outw
  assert (inw > 0)
  assert (inw < outw)
  assert (outw > 0)
  assert (param > 0)
  k = '%sP%dT%d' % (op, param, outw)
  retStr = ( '(define-fun ' + k)

  if op == 'zext':
    smt_op = 'zero_extend'
  elif op == 'sext':
    smt_op = 'sign_extend'
  else:
    assert False

  retStr += (' ((in %s)) ' % BvConstructs.width_to_type(inw) ) + BvConstructs.width_to_type(outw) + \
    ' ((_ %s %d) in)' % (smt_op, param)
  retStr += ')'
  repls = '(_ %s %d)' % (smt_op, param)
  return k, retStr, repls

def _gen_smt2(fn):
  return fn.to_smtlib(daggify = Config_smtlib2_daggify)
  


sygus_template = """

(set-logic BV)

{predefs}

(synth-fun INV 
   {args} Bool
(
    (Start Bool (Conj))
    (Conj Bool (Disj 
                (and Disj Conj)))
    (Disj Bool (Literal 
                (or Literal Disj)))
    (Literal Bool (Atom
                (not Atom)))
    (Atom Bool (
      {comps}
      ))
      {evcs}
   ))


{Fminus2}
{Tr}

{vdefs}

{blocks}
{facts}
{imply}

(check-synth)

"""

# (E0 Bool )
#    (E2 (_ BitVec 2) (V2 (bvadd E2 E2)))
#    (V2 (_ BitVec 2) (base addr cnt C2 V2))
#    (C2 (_ BitVec 2) (#b00 #b01 #b10 #b11))
# define F-2
# define Tr
# define vars

# (constraint (not (INV #b10 #b00 #b00))) # it can be fewer vars, what to do?
# (constraint (INV #b10 #b00 #b00))

# (constraint (=> (and (F-2 %allvars%) (Tr %allvars%)) (INV %vars%)))



class BvConstructs:
  def __init__(self, Vars = [], Arithms = [], Comps = [], Consts = [], Concats = [], Extracts = [], Rotates = [], Exts = [], Unary = [] ):
    self.Vars, self.Arithms, self.Comps , self.Consts , self.Concats, self.Extracts, \
      self.Rotates, self.Exts, self.Unary =  \
        Vars, Arithms, Comps, Consts, Concats, Extracts, Rotates, Exts, Unary
    # need to convert to string (op, consts, vars)
  def empty(self):
    return len(self.Vars) == 0 and len(self.Arithms) == 0 and len(self.Comps) == 0 \
      and len(self.Consts) == 0 and len(self.Concats) == 0 and len(self.Extracts) == 0 and \
      len(self.Rotates) == 0 and len(self.Exts) == 0 and len(self.Unary) == 0

  @staticmethod
  def width_to_type(width):
    assert (width >= 0)
    if width == 0:
      return 'Bool'
    return '(_ BitVec %d)' % width



# 0 for bool
#self.BvUnary = {}    # width -> set[ops]
#self.BvOps = {}      # you need to know the width also : width -> set[ops] (same width)
#self.BvComps = {}    # you need to know the width also : width -> set[ops] (same width)
#self.BvConsts = {}   # width -> set[consts (should be string already)] # const eq?
#self.BvConcats = {}  # result width -> set[(width1, width2)]
#self.BvExtracts = {} # result width -> set[(input width, h, l)]
#self.BvRotates = {}   # result width -> set[(op, param)]
#self.BvExts = {}     # result width -> set[(op, param, input width )] op 



class ItpEnhance:
    ## QUESTION: DO YOU NEED TO KNOW BLOCKED CEX F_idx_minus2 ??? 
    ## YOU CAN TRY?

    ## (prev /\ T => new ) => itp => cex_next 

    def __init__(self, itp, ctg, facts, blocked_cexs, F_idx_minus2, T, allvars, primevars):
        assert (Config_use_trans or Config_use_facts) # you have to use at least one pos example
        assert (isinstance(F_idx_minus2,list))

        self.ctg = ctg
        self.allvars = allvars
        self.primevars = primevars
        self.variable_set = _get_var(ctg)
        self.ordered_vars = sorted(list(self.variable_set))

        self.facts = _get_cubes_with_more_var(facts)  # exists a = 1 b = 1 (c ?)
        self.blocked_cexs = _get_cubes_with_fewer_var(blocked_cexs) # (not a = 1)

        _sanity_check_no_conflict(self.facts, self.blocked_cexs, self.variable_set)

        self.F_prev = F_idx_minus2
        self.T = T

        self.opextract = OpExtractor() # work on itp 
        self.opextract.walk(itp)
        
        # fix the above, you need to extract first -- fixed
        self.LangConstructs = {} # bitwidth -> BvConstructs
        self._to_bv_constructs()

        self.functs = {} # func name -> def string
        self.funct_replace = {} # func name -> text to replace
        
    def get_enhanced_itp(self):
        self.gen_sygus_query('cex-idx.smt2')
        assert (False) # need to implement here about running cvc4 and read in

    def _to_bv_constructs(self):
        # self.opextract -> self.LangConstructs

        # deal with variables 
        for v in self.variable_set:
            w = _get_unified_width(v)
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Vars.append(v.symbol_name())

        for w, ops in self.opextract.BvUnary:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Unary = ops

        for w, ops in self.opextract.BvOps:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Arithms = ops

        for w, ops in self.opextract.BvComps:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Comps = ops

        for w, consts in self.opextract.BvConsts:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Consts = consts

        for w, concats in self.opextract.BvConcats:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Concats = concats

        for w, extracts in self.opextract.BvExtracts:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Extracts = extracts

        for w, rotates in self.opextract.BvRotates:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Rotates = rotates

        for w, exts in self.opextract.BvExts:
            if w not in self.LangConstructs:
                self.LangConstructs[w] = BvConstructs()
            self.LangConstructs[w].Exts = exts

        # sanity check, when it is referring an arg, arg with that w should exist
        for w, constr in self.LangConstructs.items():
            for w1, w2 in constr.Concats:
                assert (not self.LangConstructs[w1].empty())
                assert (not self.LangConstructs[w2].empty())
            for wi, h, l in constr.Extracts:
                assert (not self.LangConstructs[wi].empty())
            for op,p,wi in constr.Exts:
                assert (not self.LangConstructs[wi].empty())


    def gen_sygus_query(self, sygus_fn):
        comps, evcs = self._to_sygus_tree()
        facts_stx = self._to_facts()
        blocks_stx = self._to_blocks()

        f_minus_2_stx = self._gen_f_minus_2()
        tr_stx = self._gen_tr()
        vp_def_stx = self._gen_def_states()
        imply_stx = self._gen_Fminus2_Tr_imply_constraint()
        predefs = '\n'.join([ _, d in self.functs.items()])
        args = _to_args( ordered_vars )

        sygus_template.format(predefs = predefs, args = args, \
            comps = comps, evcs = evcs, Fminus2 = f_minus_2_stx,\
            Tr = tr_stx, vdefs = vp_def_stx, blocks = blocks_stx,
            facts = facts_stx, imply = imply_stx)

        with open(sygus_fn, 'w') as fout:
            fout.write(sygus_template)


    def _gen_def_states(self): # -> vp_def_stx
        v_def = ['(declare-var ' + _to_name_type_suffix_no_p(v, 'V') + ')' for v in self.allvars]
        p_def = ['(declare-var ' + _to_name_type_suffix_no_p(v, 'P') + ')' for v in self.allvars]
        return ('\n'.join(v_def) + '\n' + '\n'.join(p_def))

    def _gen_Fminus2_Tr_imply_constraint(self): #
        template = '(constraint (=> (and (Fminus2 {argV}) (Tr {argV} {argP})) (INV {argP})))'
        argv = ' '.join([v.symbol_name()+'V' for v in self.allvars])
        argp = ' '.join([v.symbol_name()+'P' for v in self.allvars])
        return template.format(argV = argv, argP = argp)

    def _gen_f_minus_2(self): # -> f_minus_2_stx
        return '(define-fun Fminus2 ' + _to_args(self.allvars) + ' Bool ' + '(' + _gen_smt2(And(self.F_prev)) + '))'
        
    def _gen_tr(self): # -> tr_stx
        return '(define-fun Tr ' + _to_tr_args(self.allvars, self.primevars) + \
         ' Bool ' + '(' + _gen_smt2(And(self.F_prev)) + '))'


    def _to_blocks(self): # -> blocks_stx
        blocks_stx = []
        for cube in self.blocked_cexs:
            statement = '(constraint (not (INV'
            for v in self.ordered_vars:
                if v in cube:
                    statement += ' ' + _const_to_str(cube[v])
                else: # not in, then we have a choice
                    if Config_expand_values:
                        assert (False) # TODO: not implemented, probably not needed
                    else:
                        statement += ' ' + v.symbol_name()+'V'  # we expect it to be forall
            statement += ')))'
            blocks_stx.append(statement)
        return '\n'.join(blocks_stx)

    def _to_facts(self): # -> facts_stx
        facts_stx = []
        for cube in self.facts: # self.facts is a list of dict 
            facts_stx.append( \
                '(constraint (INV ' + \
                ' '.join([_const_to_str( cube[v] ) for v in self.ordered_vars]) + \
                '))' )
        return '\n'.join(facts_stx)

    def _to_sygus_tree(self): # generate comps, evcs # update self.funct self.funct_replace
        # for each bv, at least have the eq
        comps = []
        for width, constr in self.LangConstructs.items():
            comps.append('(= E%d E%d)' % (width, width))
            for op in constr.Comps:
                if op != '=':
                    comps.append('(%s E%d E%d)' % (op, width, width))
        comps = ' '.join(comps)

        evcs = ''

        for width, constr in self.LangConstructs.items():
            tp = BvConstructs.width_to_type(width)
            evcs += ('(E%d' % width) + ' ' + tp + ' ('
            
            if constr.Vars:
              evcs += 'V%d' % width
            if constr.Consts:
              evcs += 'C%d' % width
            if constr.Arithms or constr.Unary:
              evcs += 'Arithm%d' % width
            if constr.Concats:
              evcs += 'Concat%d' % width
            if constr.Extracts:
              evcs += 'Extract%d' % width
            if constr.Rotates:
              evcs += 'Rotate%d' % width
            if constr.Exts:
              evcs += 'Ext%d' % width

            evcs += '))\n'

            if constr.Vars:
                evcs += ('(V%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(constr.Vars) ## TODO: DEAL WITH UNDERSCORE!!!
                evcs += '))\n'
            if constr.Concats:
                evcs += ('(C%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(constr.Concats) ## TODO: DEAL WITH UNDERSCORE!!!
                evcs += '))\n'
            if constr.Arithms or constr.Unary: # include shifts
                evcs += ('(Arithm%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(['(%s E%d E%d)' % (op, width, width) for op in constr.Arithms] + \
                    ['(%s E%d)' % (op, width) for op in constr.Unary])
                evcs += '))\n'
            if constr.Concats:
                evcs += ('(Concat%d' % width) + ' ' + tp + ' ('
                evcs += ' '.join(['(concat' + (' E%d E%d' % (w1, w2)) + ')' for w1, w2 in constr.Concats])                
                evcs += '))\n'
            if constr.Extracts:
                evcs += ('(Extract%d' % width) + ' ' + tp + ' ('
                # need to define functions
                exts = []
                for inw, h, l in constr.Extracts: # whether it is necessary remains a question
                    k, fdef, repls = _gen_define_extracts(inw, h, l, width)
                    exts.append('(%s E%d)' % (k, inw))
                    if k not in self.functs:
                        self.functs[k] = fdef
                        self.funct_replace[k] = repls
                evcs += ' '.join(exts)
                evcs += '))\n'
            if constr.Rotates:
                evcs += ('(Rotate%d' % width) + ' ' + tp + ' ('
                exts = []
                for op, param in constr.Rotates: # whether it is necessary remains a question
                    k, fdef, repls = _gen_define_rotate(op, param, width)
                    exts.append('(%s E%d)' % (k, width))
                    if k not in self.functs:
                        self.functs[k] = fdef
                        self.funct_replace[k] = repls
                evcs += ' '.join(exts)               
                evcs += '))\n'
            if constr.Exts:
                evcs += ('(Ext%d' % width) + ' ' + tp + ' ('
                exts = []
                for op, param, inw in constr.Exts: # whether it is necessary remains a question
                    k, fdef, repls = _gen_define_extend(op, param, inw, width)
                    exts.append('(%s E%d)' % (k, inw))
                    if k not in self.functs:
                        self.functs[k] = fdef
                        self.funct_replace[k] = repls
                evcs += ' '.join(exts)      
                evcs += '))\n'

        return comps, evcs



# ----------------------------------------------
# let's do some test on the generation

def test():
    pass


if __name__ == '__main__':
    test()
