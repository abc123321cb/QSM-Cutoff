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
change the python version in repycudd Makefile,Makefile_64bit to your version of python3.1X
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

5. Install pysmt
```
python3 setup.py install
```
## Usage
To parse an ivy file, perform forward reachability, and enumerate prime orbits
```=python3
python3 qrm.py -i [IVY FILE] -s [sort1=size1,sort2=size2 ...]
```

