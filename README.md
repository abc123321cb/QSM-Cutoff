# py-qrm
## Installation
```
apt-get install git
git clone --recurse-submodules git@github.com:lauren-yrluo/py-qrm.git
```
1. Set up python environment (recommend python3.12 and above)
```
apt-get install python3
apt-get install pip
apt-get install python3-dev
python3 -m pip install python-sat[aiger,approxmc,cryptosat,pblib]
python3 -m pip install python-sat
python3 -m pip install z3-solver==4.8.9
python3 -m pip install pyyaml
python3 -m pip install pytest
python3 -m pip install setuptools
python3 -m pip install more-itertools
python3 -m pip install itertools
```

2. Install swig
```
apt-get install autotools-dev
apt-get install automake
apt-get install bison
cd swig-4.2.1
./autogen.sh
./configure --prefix=YOUR_PATH
make
make install
```

3. Install ivy
```
apt-get install cmake
cd ivy
python3 build_submodules.py
python3 setup.py install
python3 setup.py develop
```

### Issues with Installation
If you don't have permission to `apt-get install` or `yum install`, try the following steps:
- Download the source
- `./configure --prefix=YOUR_PATH`
- `make` and then `make install`
- `export PATH=YOUR_PATH:$PATH` so that system looks up your path first

## Usage
```=python3
./configure.sh [PYTON INCLUDE PATH] (e.g. /usr/include/python3.12)
python3 qrm.py [IVY FILE] -s [sort1=size1,sort2=size2 ...]
python3 run_all.py [YAML FILE]
```
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
- `-v 5`: 
    - print debug info
#### Experient Options
```
python3 run_all.py [YAML] -v 5 -w -l log 
```

