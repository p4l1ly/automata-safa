FROM ubuntu:focal-20210921

RUN \
  apt-get update && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y unzip wget software-properties-common cargo build-essential cmake libreadline-dev ant ivy default-jdk maven subversion libboost-dev zsh capnproto libcapnp-dev

RUN \
  ln -s -T /usr/share/java/ivy.jar /usr/share/ant/lib/ivy.jar

RUN \
  add-apt-repository -y ppa:hvr/ghc && \
  apt install -y ghc-8.10.3 cabal-install-3.4 && \
  ln -s /opt/ghc/bin/ghc /usr/local/bin/ghc && \
  ln -s /opt/ghc/bin/cabal /usr/local/bin/cabal && \
  cabal update

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
  download jurajsic symbolicautomata 0150d2f8adf509ff48fe8f47fcd19f135582df17 && \
  download jurajsic afaminisat 41288a30262223dbb0a50035e8c51da0ef6b7786 && \
  download jurajsic emptiness-brics 94cdb95f8ee95b0b524c6b6041d693e0b77e6ce5 && \
  rm /tmp/download.zip && \
  mkdir automata-safa

# this is probably not needed anymore (only if haskell needs it?)
# RUN \
#   cd automata-safa-capnp && \
#   cmake -S . -B build && \
#   cmake --build build && \
#   cmake --install build

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

RUN \
  cd emptiness-brics && \
  svn package

ADD automata-safa.cabal Cargo.lock Cargo.toml CHANGELOG.md LICENSE Setup.hs automata-safa/
ADD app/ automata-safa/app/
ADD src/ automata-safa/src/
ADD test/ automata-safa/test/

RUN echo 'packages: lens-recursion-schemes automata-safa-capnp automata-safa ltl-translators' > cabal.project
RUN cd automata-safa && cargo build --release && cp target/release/libautomata_safa.so /usr/lib
RUN cabal install ltle-to-afa ltl-generator-exe ltl-randgen-exe
RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.bashrc
RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.zshrc
ENV LANG='C.UTF-8' LANGUAGE='' LC_ALL='C.UTF-8'
