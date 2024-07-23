from ivy import ivy_utils as iu
from ivy import ivy_init
from ivy import ivy_module as im
from ivy import ivy_isolate
from ivy import ivy_ast
from verbose import *

def init_isolate():
    temporals = [p for p in im.module.labeled_props if p.temporal]
    mod = im.module
    if temporals:
        if len(temporals) > 1:
            raise iu.IvyError(None,'multiple temporal properties in an isolate not supported yet')
        from ivy.ivy_l2s import l2s
        l2s(mod, temporals[0])
        mod.concept_spaces = []
        mod.update_conjs()
    with im.module.theory_context():
        pass

def init_ivy_module(options):
    isolates = sorted(list(im.module.isolates))
    done_isolates = 0
    for isolate in isolates:
        if isolate != None and isolate in im.module.isolates:
            idef = im.module.isolates[isolate]
            if len(idef.verified()) == 0 or isinstance(idef,ivy_ast.TrustedIsolateDef):
                continue # skip if nothing to verify
        if isolate:
            vprint(options, f'\nPrinting isolate {isolate}:', 5)
        if done_isolates >= 1:
            raise iu.IvyError(None,"Expected exactly one isolate, got %s" % len(isolates))
        with im.module.copy():
            ivy_isolate.create_isolate(isolate) # ,ext='ext'
            init_isolate()
            done_isolates += 1
    return im.module

def parse_ivy(options, ivy_filename):
    import signal
    signal.signal(signal.SIGINT,signal.SIG_DFL)
    from ivy import ivy_alpha
    ivy_alpha.test_bottom = False # this prevents a useless SAT check
    vprint_title(options, 'Parsing Ivy', 5)
    ivy_init.read_params()
    ivy_module = None
    with im.Module():
        with iu.ErrorPrinter():
            ivy_init.source_file(ivy_filename,ivy_init.open_read(ivy_filename), create_isolate=False)
            ivy_module = init_ivy_module(options)
    vprint(options, 'OK', 5)
    import sys
    sys.stdout.flush()
    return ivy_module
