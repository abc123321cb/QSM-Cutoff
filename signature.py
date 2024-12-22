from qutil import *
from verbose import *
from util import QrmOptions
from itertools import product
from typing import List, Dict, Set
from ivy import ivy_logic as il
from more_itertools import set_partitions

'''
Given a list of terms with arguments,
encode how each argument info into "signature":
    sort        : the argument's sort
    signed_fname: the literal phase and name of the function it appears
    arg_id      : the index of argument it appears in a function
    func_id     : signed_fname may appear multiple times, func_id is the index of appearance
'''
class ArgumentSignature():
    def __init__(self, sort, signed_fname, func_id, arg_id):
        self.sort              : il.EnumeratedSort = sort
        self.signed_fname      : str = signed_fname
        self.func_id           : int = func_id
        self.arg_id            : int = arg_id
        self.signature         : str = f'{self.sort.name}{SIGNATR_DELIM}{self.signed_fname}{SIGNATR_DELIM}{self.arg_id}{SIGNATR_DELIM}{self.func_id}'
        self.reduced_signature : str = f'{self.sort.name}{SIGNATR_DELIM}{self.signed_fname}{SIGNATR_DELIM}{self.arg_id}'

    def get_reduced_signature(self) -> str: # rm func_id
        return self.reduced_signature

    def __str__(self):
        return self.signature

    def __repr__(self):
        return str(self) 

class ClassSignature():
    def __init__(self, arg_signatures: List[ArgumentSignature]):
        arg_signatures.sort(key=lambda sig: str(sig))
        self.arg_signatures    : List[ArgumentSignature] = arg_signatures
        self.signature         : str = CLASS_DELIM.join([str(sig) for sig in arg_signatures])
        self.reduced_signature : str = CLASS_DELIM.join([sig.get_reduced_signature() for sig in arg_signatures])

    def get_reduced_signature(self): # rm func_id in each arg_signature
        return self.reduced_signature

    def __str__(self):
        return self.signature

    def __repr__(self):
        return str(self)

class SortPartitionSignature():
    def __init__(self, class_signatures: List[ClassSignature]):
        class_signatures.sort(key=lambda sig: str(sig))
        self.class_signatures   : List[ClassSignature] = class_signatures 
        self.signature          : str = PARTITION_DELIM.join([str(sig) for sig in class_signatures])
        self.reduced_signature  : str = PARTITION_DELIM.join([sig.get_reduced_signature() for sig in class_signatures])

    def get_reduced_signature(self): # rm func_id in each arg_signature
        return self.reduced_signature

    def __str__(self):
        return self.signature

    def __repr__(self):
        return str(self)

class SortPartitionSignature_(SortPartitionSignature):
    def __init__(self, class_signatures : List[ClassSignature]):
        SortPartitionSignature.__init__(self, class_signatures)
        # reduced signatures
        self.identical_classes    : Dict[str, List[ClassSignature]] = {} # group self.class_sigs into classes according to their reduced_class_sig
        self._set_identical_classes()
        self.identical_single_classes : Dict[str, ClassSignature] = {}
        self.identical_multi_classes  : Dict[str, List[ArgumentSignature]] = {} # all arguments that hold the multi-class constants
        self._set_identical_single_multi_classes()
        # quantification-pattern inference
        self.forall_class_sigs : List[ClassSignature] = []
        self.exists_class_sigs : List[ClassSignature] = []

    def _set_identical_classes(self):
        for sig in self.class_signatures:
            reduced_sig = sig.get_reduced_signature()
            if not reduced_sig in self.identical_classes:
                self.identical_classes[reduced_sig] = []
            self.identical_classes[reduced_sig].append(sig)

    def _set_identical_single_multi_classes(self):
        for identical_key, class_sigs in self.identical_classes.items():
            if len(class_sigs) == 1:
                self.identical_single_classes[identical_key] = class_sigs[0]
            else:
                arg_signatures = []
                for class_sig in class_sigs:
                    arg_signatures += class_sig.arg_signatures
                self.identical_multi_classes[identical_key] = arg_signatures 
        assert(len(self.identical_single_classes) + len(self.identical_multi_classes) == len(self.identical_classes))

    def __str__(self):
        return SortPartitionSignature.__str__(self)

    def __repr__(self):
        return str(self)

class PartitionSignature():
    def __init__(self, sort2sig : Dict[il.EnumeratedSort, SortPartitionSignature]): 
        sort_sigs     = []
        red_sort_sigs = []
        sort2sig = dict(sorted(sort2sig.items()))
        for sort, sig in sort2sig.items():
            sort_sigs.append([str(sig)])
            red_sort_sigs.append([sig.get_reduced_signature()])
        self.sort2signature = sort2sig 
        self.signature          = list(product(*sort_sigs))[0]
        self.reduced_signature  = list(product(*red_sort_sigs))[0]

    def get_reduced_signature(self): # rm func_id in each arg_signature
        return self.reduced_signature

    def __str__(self):
        return str(self.signature)

    def __repr__(self):
        return str(self)

from itertools import permutations


class SigGenerator():
    def __init__(self, terms, options : QrmOptions):
        self.func_name2symbol     = {}  # unsigned function name -> function symbol
        self.func_name2args_sort  = {}  # unsigned function name -> arguments' sorts
        self.sign_func_name2count = {}  # signed function name   -> count of appearance 
        self._initialize(terms, options)

    def _add_func_name_to_symbol(self, fname, symbol):
        self.func_name2symbol[fname] = symbol

    def _add_func_name_to_args_sort(self, fname, args_sort):
        self.func_name2args_sort[fname] = args_sort

    def _add_signed_func_name_count(self, sfname):
        if not sfname in self.sign_func_name2count: 
            self.sign_func_name2count[sfname] = 0
        self.sign_func_name2count[sfname] += 1

    def _get_args_sort_from_signed_func_name(self, sfname):
        (_, fname) = split_signed_func_name(sfname)
        return self.func_name2args_sort[fname]

    def _initialize(self, terms, options):
        for term  in terms:
            (sign,atom) = split_term(term)
            func_symbol = get_func_symbol(atom)
            fname       = get_unsigned_func_name(atom, func_symbol)
            sfname      = get_signed_func_name(sign, atom, func_symbol) 
            args_sort   = get_func_args_sort(atom, func_symbol)
            self._add_func_name_to_symbol(fname, func_symbol)
            self._add_func_name_to_args_sort(fname, args_sort)
            self._add_signed_func_name_count(sfname)

        vprint_title(options, 'SigGenerator', 5)
        vprint(options, f'terms:  {[str(term) for term in terms]}', 5)
        vprint(options, f'func_name2symbol:  {self.func_name2symbol}', 5)
        vprint(options, f'func_name2args_sort:  {self.func_name2args_sort}', 5)
        vprint(options, f'sign_func_name2count:  {self.sign_func_name2count}', 5)

    def generate_argument_signature(self):
        for sfname, func_count in self.sign_func_name2count.items():
            args_sort = self._get_args_sort_from_signed_func_name(sfname)
            for func_id in range(func_count):
                for arg_id, sort in enumerate(args_sort):
                    yield ArgumentSignature(sort, sfname, func_id, arg_id)

'''
Given a list of terms with arguments,
each argument holds a constant 
bind each argument signature to the variable it is holding
different signature may bind to same constant 
'''
class ConstArgBinding():
    def __init__(self, terms, options):
        self.sign_func_name2args  : Dict[str, List[il.Symbol]] = {}  
            # signed function name -> [arg_list1, arg_list2]
            # each arg_list consists of consts 
        # binding
        self.const2sigs : Dict[il.Symbol, ArgumentSignature]  = {}
        self.sig2const  : Dict[str, il.Symbol]                = {}

        self._initialize(terms)
        self._bind_each_const_to_argument_signatures()

        vprint_title(options, 'ConstArgBinding', 5)
        vprint(options, f'terms: {[str(term) for term in terms]}', 5)
        vprint(options, f'sign_func_name2args: {self.sign_func_name2args}', 5)
        vprint(options, f'const2sigs: {self.const2sigs}', 5)
        vprint(options, f'sig2const: {self.sig2const}', 5)

    def _add_signed_func_name_args(self, sfname : str, args : List[il.Symbol]):
        if not sfname in self.sign_func_name2args: 
            self.sign_func_name2args[sfname] = [] 
        self.sign_func_name2args[sfname].append(args)

    def _initialize(self, terms):
        for term in terms:
            (sign, atom)  = split_term(term)
            fsymbol = get_func_symbol(atom)
            sfname  = get_signed_func_name(sign, atom, fsymbol) 
            args    = get_func_args(atom) 
            self._add_signed_func_name_args(sfname, args)

    def _bind_const_signature_pair(self, const : il.Symbol, sig : ArgumentSignature):
        if not const in self.const2sigs:
            self.const2sigs[const] = [] 
        self.const2sigs[const].append(sig)
        self.sig2const[str(sig)] = const 

    def _bind_each_const_to_argument_signatures(self):
        for sfname, args_list in self.sign_func_name2args.items():
            for func_id, args in enumerate(args_list):
                for arg_id, const in enumerate(args):
                    sig = ArgumentSignature(const.sort, sfname, func_id, arg_id)
                    self._bind_const_signature_pair(const, sig)

    #------------------------------------------------------------
    # public method
    #------------------------------------------------------------
    def get(self):
        for const, arg_sigs in self.const2sigs.items():
            yield (const, arg_sigs)

'''
Given a variable and argument signatures binding representing how variables appear in arugments,
group argument signatures associated with same const into the same "class",
which forms a "partition" consisting of classes of argument signatures
'''
class ArgPartition():
    def __init__(self, binding : ConstArgBinding, options : QrmOptions):
        self.binding = binding      
        
        # sort2class_sigs
        self.sort2class_sigs : Dict[il.EnumeratedSort, List[ClassSignature]] = {}
        self._set_sort_to_class_signatures()

        # sort2part_sig
        self.sort2part_sig : Dict[il.EnumeratedSort, SortPartitionSignature] = {}
        self._set_sort_to_partition_signature()

        # part_sig
        self.part_sig = PartitionSignature(self.sort2part_sig)

        vprint_title(options, 'ArgPartition', 5)
        vprint(options, f'sort2class_sigs: {self.sort2class_sigs}', 5)
        vprint(options, f'sort2part_sig: {self.sort2part_sig}', 5)
        vprint(options, f'part_sig: {self.part_sig}', 5)

    def _add_sort_class_signature(self, sort : il.EnumeratedSort, class_sig : ClassSignature):
        if not sort in self.sort2class_sigs:
            self.sort2class_sigs[sort] = []
        self.sort2class_sigs[sort].append(class_sig)

    def _set_sort_to_class_signatures(self):
        for (const, arg_sigs) in self.binding.get():
            class_sig = ClassSignature(arg_sigs)
            self._add_sort_class_signature(const.sort, class_sig)

    def _set_sort_to_partition_signature(self):
        for sort, class_sigs in self.sort2class_sigs.items():
            part_sig = SortPartitionSignature(class_sigs)
            self.sort2part_sig[sort] = part_sig 

    #------------------------------------------------------------
    # public method
    #------------------------------------------------------------
    def get_partition_signature(self):
        return str(self.part_sig)

'''
Given a set of variable and argument signatures bindings {b0, b1, ...}
each argument signature is associated with v0 in b0, v1 in b1, ...
group argument signatures associated with same product const (v0, v1, ...) into same "class" 
which forms a "partition" consisting of classes of argument signatures
'''
class ProductArgPartition():
    def __init__(self, sig_gen : SigGenerator, bindings : List[ConstArgBinding], options : QrmOptions):
        self.sig_gen  : SigGenerator     = sig_gen
        self.bindings : List[ConstArgBinding] = bindings
        # sort2classes
        self.sort2classes                   = {}
        # sort2class_sigs
        self.sort2class_sigs : Dict[il.EnumeratedSort, List[ClassSignature]] = {}
        self._set_sort_to_class_signatures()
        # sort2part_sig
        self.sort2part_sig : Dict[il.EnumeratedSort, SortPartitionSignature_] = {}
        self._set_sort_to_partition_signature()

        vprint_title(options, 'ProductArgPartition', 5)
        vprint(options, f'sort2class_sigs: {self.sort2class_sigs}', 5)
        vprint(options, f'sort2part_sig: {self.sort2part_sig}', 5)
        for sort, part_sig in self.sort2part_sig.items():
            vprint(options, f'\tsort: {sort.name}', 5)
            vprint(options, f'\tidentical_classes: {part_sig.identical_classes}', 5)
            vprint(options, f'\tidentical_single_classes: {part_sig.identical_single_classes}', 5)
            vprint(options, f'\tidentical_multi_classes: {part_sig.identical_multi_classes}', 5)

    def _get_const_product(self, signature : ArgumentSignature):
        consts = []
        for bid, binding in enumerate(self.bindings):
            const = binding.sig2const[str(signature)]
            consts.append(f'{str(const)}.{bid}')
        return '.'.join(consts)

    def _add_sort_signature(self, sort, const_product, signature : ArgumentSignature):
        if not sort in self.sort2classes:
            self.sort2classes[sort] = {} 
        if not const_product in self.sort2classes[sort]:
            self.sort2classes[sort][const_product] = []
        self.sort2classes[sort][const_product].append(signature)

    def _set_sort_to_class_signatures(self):
        for sig in self.sig_gen.generate_argument_signature():
            const_product = self._get_const_product(sig)
            self._add_sort_signature(sig.sort, const_product, sig)
        for sort, classes in self.sort2classes.items():
            class_signatrs = []
            for sigs in classes.values():
                class_signatr = ClassSignature(sigs)
                class_signatrs.append(class_signatr)
            class_signatrs.sort(key=lambda sig : str(sig))
            self.sort2class_sigs[sort] = class_signatrs

    def _set_sort_to_partition_signature(self):
        for sort, class_sigs in self.sort2class_sigs.items():
            part_sig = SortPartitionSignature_(class_sigs)
            self.sort2part_sig[sort] = part_sig 

def get_permuted_signature(sig, sign_func_name2id, func_perm):
    if isinstance(sig, ArgumentSignature):
        fname_id      = sign_func_name2id[sig.signed_fname]
        new_func_id   = func_perm[fname_id][sig.func_id]
        return ArgumentSignature(sig.sort, sig.signed_fname, new_func_id, sig.arg_id)
    elif isinstance(sig, ClassSignature):
        permuted_arg_sigs = [get_permuted_signature(s, sign_func_name2id, func_perm) for s in sig.arg_signatures]
        return ClassSignature(permuted_arg_sigs)
    elif isinstance(sig, SortPartitionSignature):
        permuted_class_sigs = [get_permuted_signature(s, sign_func_name2id, func_perm) for s in sig.class_signatures]
        return SortPartitionSignature(permuted_class_sigs)  
    elif isinstance(sig, PartitionSignature):
        sort2sig : Dict[il.EnumeratedSort, SortPartitionSignature] = {} 
        for sort, s in sig.sort2signature.items():
            sort2sig[sort] = get_permuted_signature(s, sign_func_name2id, func_perm)
        return PartitionSignature(sort2sig)

def merge_class_signatures(class_sigs: List[ClassSignature]) -> ClassSignature:
    arg_sigs = []
    for class_sig in class_sigs:
        arg_sigs += class_sig.arg_signatures
    return ClassSignature(arg_sigs)

'''
Given a list of class_sigs, enumerate all partitions of class_sigs
In each partition, merge the class_sigs grouped into same class into a larger class_sig.
Return the sort_partition_sigs consisting of merged class_sigs
'''
def enumerate_sort_partitions(sort : il.EnumeratedSort, class_sigs : List[ClassSignature]) -> List[SortPartitionSignature]:
    class_sigs.sort(key=lambda sig: str(sig))
    sort_partitions = []
    partitions      = list(set_partitions(class_sigs))
    red_part_sigs   = set()
    for partition in partitions:
        if len(partition) <= sort.card: # skip the ones with number of classes > |sort|
            merged_class_sigs = []
            for class_sigs in partition:
                class_sig = merge_class_signatures(class_sigs)
                merged_class_sigs.append(class_sig)
            sort_partition = SortPartitionSignature(merged_class_sigs)
            sort_partitions.append(sort_partition)
    return sort_partitions

'''
Given all sort_partition_sigs, return all set of partition_sig
'''
def get_partitions_from_sort_partititions(sort2part_sigs : Dict[il.EnumeratedSort, List[SortPartitionSignature]]) -> List[PartitionSignature]:
    sort_sigs = []
    for sort, sigs in sort2part_sigs.items():
        sort_sigs.append(sigs)
    product_sigs = list(product(*sort_sigs))
    partition_sigs = [] 
    for prod_sig in product_sigs: 
        sort2part_sig = {}
        for sort_id, sort in enumerate(sort2part_sigs.keys()):
            sort2part_sig[sort] = prod_sig[sort_id]
        partition_sig = PartitionSignature(sort2part_sig)
        partition_sigs.append(partition_sig)
    return partition_sigs