# QSM-Cutoff
## Installation
```
git clone --recurse-submodules git@github.com:QSM-Cutoff/QSM-Cutoff.git
```
1. Set up python environment (recommend python3.12 and above)
```
python3 -m pip install python-sat[aiger,approxmc,cryptosat,pblib]
python3 -m pip install python-sat
python3 -m pip install z3-solver
python3 -m pip install pyyaml
python3 -m pip install pytest
python3 -m pip install setuptools
python3 -m pip install more-itertools
python3 -m pip install itertools
python3 -m pip install numpy
```

2. Install swig
- Install `autotools-dev`, `automake`, `bison`.
```
cd swig-4.2.1
./autogen.sh
./configure --prefix=YOUR_PATH
make
make install
```

3. Install repycudd
```
cd repycudd
cd cudd-2.4.2
make
make libso
cd ..
```
- Change the python version in repycudd Makefile,Makefile_64bit to your version of python3.1X and add the compilation flag `-I[PATH TO Python.h]`
```
make
export PYTHONPATH=$PYTHONPATH:[path to repycudd.py]
```

4. Install ivy
```
cd ivy
python3 build_submodules.py
python3 setup.py install
python3 setup.py develop
```

5. Install MARCO
```
cd MARCO/src/pyminisolvers
make
make test
```

## Usage
```=python3
./configure.sh [PATH TO Python.h]
python3 QSM-Cutoff.py [IVY FILE] -s [sort1=size1,sort2=size2 ...]
```
- Run `python3 QSM-Cutoff.py -h` for more information

## Scripts
The directory `scripts` contains the scripts for generating results of our CAV 2025 paper.

## Logs
The directory `CAV_logs` contains experiment logs of our CAV 2025 paper.

## Check installation
To check the installion copy paste this to your terminal.
```
python3 - <<'PY'
import importlib, sys
pkgs = [
    "pysat",                      # python-sat[…]
    "z3",                         # z3-solver
    "yaml",                       # pyyaml
    "pytest", "setuptools",
    "more_itertools", "numpy",
]                             
missing = []
for p in pkgs:
    try:
        importlib.import_module(p)
    except ImportError:
        missing.append(p)
if missing:
    print("❌  Missing:", ", ".join(missing))
    sys.exit(1)                              
print("✅  All listed Python packages import correctly.")
PY
```
