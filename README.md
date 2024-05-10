# py-qrm
## Installation
```
apt-get install git
git clone --recurse-submodules git@github.com:lauren-yrluo/py-qrm.git
```
1. Set up python environment (recommend python3.11 and above)
```
apt-get install python3
apt-get install pip
apt-get install python3-dev
pip install python-sat[aiger,approxmc,cryptosat,pblib]
pip install python-sat
pip install z3-solver==4.8.9
pip install pyyaml
pip install pytest
pip install setuptools
```

2. Install swig
```
apt-get install autotools-dev
apt-get install automake
apt-get install bison
cd swig-4.2.1
./autogen.sh
./configure --without-pcre
make
make install
```
3. Install repycudd
```
cd repycudd
cd cudd-2.4.2
make
make libso
cd..
```

change the python version in repycudd Makefile,Makefile_64bit to your version of python3.1X and add the compilation flag `-I[PATH TO Python.h]`
```
make
export PYTHONPATH=$PYTHONPATH:[path to repycudd.py]
```

4. Install ivy
```
apt-get install cmake
cd ivy
python3 build_submodules.py
python3 setup.py develop
```

5. Install pysmt
```
python3 setup.py install
```
### Issues with Installation
If you don't have permission to `apt-get install` or `yum install`, try the following steps:
- Download the source
- `./configure --prefix=/home/USERNAME/opt`
- `make` and then `make install`
- `export PATH=/home/USERNAME/opt/bin/:$PATH` so that system looks up your path first

## Usage
```=python3
python3 qrm.py -i [IVY FILE] -s [sort1=size1,sort2=size2 ...]
python3 run_all.py [YAML FILE]
```
Note that 'qrm.py -y [YAML FILE]' option is buggy, use 'run_all.py [YAML FILE]' as a work around.
### Usage for Options
#### Verbosity
- default: only prints `ivy_check` result for each size, and the final qrm result
- `-v 1`: prints elapsed time
- `-v 2`: 
    - print number of variables, reachable states, orbits, suborbits, primes, minimal solutions, etc
    - number of suborbits is meaningful only if using option `-m`
    - number of minimal solutions is meaningful only if using option `-a`
- `-v 3`:
    - prints results of forward reachability
    - prints results of prime orbit generation
    - prints results of quantifier inference
    - prints results of minimization (prints all solutions if using option `-a`)
- `-v 4`:
    - prints quantifier inference result for representative prime of each suborbit
- `-v 5`: 
    - print debug info
#### Experient Options
```
python3 run_all.py [YAML] -v 1 -w       -l log    # write .ptcl, .pis, .qpis, .ivy
python3 run_all.py [YAML] -v 4 -w -a    -l log    # find all solutions, don't merge suborbits
python3 run_all.py [YAML] -v 4 -w -a -m -l log    # find all solutions, merge suborbits
```

