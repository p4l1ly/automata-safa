FROM ubuntu:focal-20210921

ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=Europe/Prague

RUN \
  apt-get update -y && \
  apt-get install -y --no-install-recommends \
    unzip \
    wget \
    software-properties-common \
    cargo \
    build-essential \
    cmake \
    libreadline-dev \
    ant \
    ivy \
    default-jdk \
    maven \
    subversion \
    libboost-dev \
    zsh \
    capnproto \
    libcapnp-dev \
    curl \
    libnuma-dev \
    zlib1g-dev \
    libgmp-dev \
    libgmp10 \
    git \
    wget \
    lsb-release \
    gnupg2 \
    apt-transport-https \
    gcc \
    autoconf \
    automake

ARG GPG_KEY=7784930957807690A66EBDBE3786C5262ECB4A3F
RUN gpg --batch --keyserver keys.openpgp.org --recv-keys $GPG_KEY

# install ghcup
RUN \
    curl https://downloads.haskell.org/~ghcup/x86_64-linux-ghcup > /usr/bin/ghcup && \
    chmod +x /usr/bin/ghcup && \
    ghcup config set gpg-setting GPGStrict

# install GHC and cabal
RUN ghcup -v install ghc --isolate /usr/local --force 8.10.7
RUN ghcup -v install ghc --isolate /usr/local --force 9.4.4
RUN ghcup -v install cabal --isolate /usr/local/bin --force latest
RUN cabal update

RUN ln -s -T /usr/\share/java/ivy.jar /usr/share/ant/lib/ivy.jar

WORKDIR /root

RUN \
  download() { \
    { \
      wget https://github.com/$1/$2/archive/$3.zip -O /tmp/download.zip && \
      unzip /tmp/download.zip && \
      mv $2-$3 $2 && \
      return 0; \
    } || return 1; \
  }; \
  download zimmski aiger ba826db1798022fdabe2de71ea173bd2b6dcac9d && \
  download berkeley-abc abc e463930709e964aede28851114edb77b10d95501 && \
  cd aiger && ./configure && make && \
  cd ~/abc && cmake -S . -B build && cmake --build build

RUN \
  download() { \
    { \
      wget https://github.com/$1/$2/archive/$3.zip -O /tmp/download.zip && \
      unzip /tmp/download.zip && \
      mv $2-$3 $2 && \
      return 0; \
    } || return 1; \
  }; \
  wget https://es-static.fbk.eu/tools/nuxmv/downloads/nuXmv-2.0.0-linux64.tar.gz && \
  tar xzf nuXmv-2.0.0-linux64.tar.gz && \
  rm nuXmv-2.0.0-linux64.tar.gz && \
  download p4l1ly lens-recursion-schemes 2dfdf5ec637f8139e3d4cd4b1f0c9803e0477543 && \
  download p4l1ly automata-safa-capnp 38437d30a98ab5b77d0122cc2c82da5cac7cfc07 && \
  download p4l1ly ltl-translators cda4316523d836bd7139a0363d80768fbc3d556b && \
  download p4l1ly JAltImpact db157709c2c85142b95b95862c8145262c100109 && \
  mkdir v2 && \
  cd v2 && \
  download p4l1ly automata-safa 348afb9f3817ef1ba0196cc2cd19d7533df48d78 && \
  download p4l1ly inversion-of-control 2301866ad6b8616885b0ba1c0f5a4ea20f6902cf && \
  cd .. && \
  download jurajsic symbolicautomata 0150d2f8adf509ff48fe8f47fcd19f135582df17 && \
  download jurajsic afaminisat 41288a30262223dbb0a50035e8c51da0ef6b7786 && \
  download jurajsic emptiness-brics 94cdb95f8ee95b0b524c6b6041d693e0b77e6ce5 && \
  rm /tmp/download.zip && \
  mkdir automata-safa

RUN apt-get install -y pkg-config
RUN \
  cd afaminisat && \
  cmake -S . -B build && \
  cmake --build build

RUN cd JAltImpact && ant resolve && ant build && cp lib/libmathsat5j-5.6.3-sosy0.so /usr/lib/libmathsat5j.so

RUN \
  cd symbolicautomata/automatark && \
  svn export -r95 https://github.com/lorisdanto/automatark/trunk/Parsers && \
  svn export -r95 https://github.com/lorisdanto/automatark/trunk/pom.xml && \
  cd .. && mvn package

ADD automata-safa.cabal Cargo.lock Cargo.toml CHANGELOG.md LICENSE Setup.hs automata-safa/
ADD app/ automata-safa/app/
ADD src/ automata-safa/src/
ADD test/ automata-safa/test/

RUN echo 'packages: lens-recursion-schemes automata-safa-capnp automata-safa ltl-translators' > cabal.project
RUN cd automata-safa && cargo build --release && cp target/release/libautomata_safa.so /usr/lib
RUN cabal install ltle-to-afa ltl-generator-exe ltl-randgen-exe --with-ghc /usr/local/bin/ghc-8.10.7

RUN echo 'packages: automata-safa inversion-of-control' > v2/cabal.project
RUN cd v2 && cabal install automata-safa-one --with-ghc /usr/local/bin/ghc-9.4.4

RUN \
  cd emptiness-brics && \
  mvn package

RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.bashrc
RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.zshrc
ENV LANG='C.UTF-8' LANGUAGE='' LC_ALL='C.UTF-8'
