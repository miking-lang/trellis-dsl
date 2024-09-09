FROM nvidia/cuda:11.7.1-runtime-ubuntu18.04

SHELL ["/bin/bash", "-c"]

WORKDIR /root

# Add a nice PS1 for bash
RUN echo "export PS1='\[\e]0;\u@\h: \w\a\]\[\033[01;32m\]\u@\h\[\033[00m\]:\[\033[01;34m\]\w\[\033[00m\]\$ '" >> /root/.bashrc

# Where the built mi image will be placed
RUN echo "export PATH=/root/.local/bin:\$PATH" >> /root/.bashrc

# Install dependencies and opam (also need to add the Nvidia key)
RUN DEBIAN_FRONTEND=noninteractive echo "Installing dependencies" \
 && apt-key adv --fetch-keys https://developer.download.nvidia.com/compute/cuda/repos/ubuntu1804/x86_64/3bf863cc.pub \
 && apt-get update \
 && ln -fs /usr/share/zoneinfo/Etc/UTC /etc/localtime \
 && apt-get install -y curl wget time cmake unzip git rsync m4 mercurial libopenblas-dev liblapacke-dev pkg-config zlib1g-dev python3 libpython3-dev libtinfo-dev libgmp-dev build-essential libffi-dev libgmp-dev libgmp10 libncurses-dev libncurses5 libtinfo5 autoconf user-setup z3 libhdf5-dev libpython3.7 libboost-dev libboost-filesystem-dev libboost-system-dev libboost-program-options-dev \
 && curl -L -o /usr/local/bin/opam https://github.com/ocaml/opam/releases/download/2.1.2/opam-2.1.2-x86_64-linux \
 && chmod +x /usr/local/bin/opam

# NOTE: Running the opam setup as a single step to contain the downloading and
#       cleaning of unwanted files in the same layer.
# 1. Initialize opam
RUN opam init --disable-sandboxing --auto-setup \
# 2. Create the 5.0.0~rc1 environment
 && opam switch create miking-ocaml 5.0.0 \
# 3. Install ocaml packages
 && opam install -y dune linenoise pyml toml lwt ocamlformat.0.24.1 \
# 4. Clean up stuff we no longer need
 && opam clean -rca \
 && rm -rf /root/.opam/repo           \
           /root/.opam/download-cache \
           /root/.opam/default

# Add the opam environment as default
RUN echo "eval \$(opam env)" >> /root/.bashrc

WORKDIR /root

# Export the opam env contents to docker ENV
ENV PATH="/root/.opam/miking-ocaml/bin:/root/.local/bin:$PATH"
ENV MANPATH="$MANPATH:/root/.opam/miking-ocaml/man"
ENV OPAM_SWITCH_PREFIX="/root/.opam/miking-ocaml"
ENV CAML_LD_LIBRARY_PATH="/root/.opam/miking-ocaml/lib/stublibs:/root/.opam/miking-ocaml/lib/ocaml/stublibs:/root/.opam/miking-ocaml/lib/ocaml"
ENV OCAML_TOPLEVEL_PATH="/root/.opam/miking-ocaml/lib/toplevel"
ENV PKG_CONFIG_PATH="/root/.opam/miking-ocaml/lib/pkgconfig"

# Install Miking
RUN mkdir -p /src \
 && cd /src \
 && git clone https://github.com/miking-lang/miking.git \
 && cd /src/miking \
 && git checkout fdce4618293c562bb56eb01028bb4db3358a5ddf

WORKDIR /src/miking

RUN eval $(opam env)   \
 && make install       \
 #&& make test          \ Skip running tests to speed up installation
 && make clean

WORKDIR /root

# Install Trellis and initialize submodules (zipHMM)
RUN cd /src \
 && git clone https://github.com/larshum/trellis-dsl.git \
 && cd /src/trellis-dsl \
 && git checkout e1c9982657bb1d940ccd9d4bdbc8940212159b0f \
 && git submodule init \
 && git submodule update

WORKDIR /src/trellis-dsl

RUN eval $(opam env) \
 && make install     \
 #&& make test        \ Skip running tests to speed up installation
 && make clean

#####################################
# INSTALLING BENCHMARK DEPENDENCIES #
#####################################

# Install Anaconda
RUN mkdir -p /root/miniconda3 \
 && wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh -O /root/miniconda3/miniconda.sh \
 && bash /root/miniconda3/miniconda.sh -b -u -p /root/miniconda3 \
 && rm /root/miniconda3/miniconda.sh

ENV PATH="/root/miniconda3/condabin:$PATH"

# Initialize the trellis-bench conda environment and use it by default.
WORKDIR /src/trellis-dsl/benchmarks
RUN conda init bash \
 && conda env create -f condaenv-trellis.yml

# Install StochHMM
WORKDIR /src
RUN git clone https://github.com/KorfLab/StochHMM.git
WORKDIR /src/StochHMM
RUN ./configure \
 && make \
 && cp stochhmm /root/.local/bin/

WORKDIR /src/trellis-dsl/benchmarks/forward/ziphmm/ziphmm
# Replace references to cblas or atlas with openblas
RUN sed -i 's/cblas atlas/openblas/g' zipHMM/CMakeLists.txt \
 && cmake . \
 && make \
 && bin/calibrate \
 && make install \
 && cp zipHMM/libpyZipHMM.so zipHMM/pyZipHMM

# KTHDNA
WORKDIR /src/trellis-dsl/benchmarks/viterbi/native-cuda/KTHDNA
SHELL ["conda", "run", "-n", "trellis-bench", "/bin/bash", "-c"]
# Temporarily remove h5py as it messes up paths when building KTHDNA.
RUN conda remove h5py \
 && make \
 && conda install h5py

WORKDIR /src/trellis-dsl/benchmarks
SHELL ["/bin/bash", "-c"]
RUN echo "conda activate trellis-bench" >> /root/.bashrc
