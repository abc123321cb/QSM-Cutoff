# QSM-Cutoff
## Installation
```
apt-get install git
git clone --recurse-submodules git@github.com:QSM-Cutoff/QSM-Cutoff.git
```
1. Set up python environment (recommend python3.12 and above)
```
apt-get install python3
apt-get install pip
apt-get install python3-dev
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
python3 setup.py install
python3 setup.py develop
```

5. Install MARCO
```
cd MARCO/src/pyminisolvers
make
make test
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
python3 QSM-Cutoff.py [IVY FILE] -s [sort1=size1,sort2=size2 ...]
```
