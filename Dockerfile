FROM ubuntu:focal-20210921

RUN \
  apt-get update && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y unzip wget software-properties-common capnproto libcapnp-dev && \
  add-apt-repository -y ppa:hvr/ghc && \
  apt install -y ghc-8.10.3 cabal-install-3.4 && \
  ln -s /opt/ghc/bin/ghc /usr/local/bin/ghc && \
  ln -s /opt/ghc/bin/cabal /usr/local/bin/cabal && \
  cabal update

RUN mkdir app
WORKDIR /app

RUN \
  download() { \
    { \
      wget https://github.com/$1/$2/archive/$3.zip -O /tmp/download.zip && \
      unzip /tmp/download.zip && \
      mv $2-$3 $2 && \
      return 0; \
    } || return 1; \
  }; \
  download p4l1ly lens-recursion-schemes 2dfdf5ec637f8139e3d4cd4b1f0c9803e0477543 && \
  download p4l1ly automata-safa-capnp a653f64a60857f53491d14e5d8923281ef75d36b && \
  download p4l1ly automata-safa af90d5a1ef3b12b8e5cad962f61804afd2d9acaa && \
  download p4l1ly ltl-translators 790508599c04df55a2b862eb13611ef9d9d5fd41 && \
  download p4l1ly automata-safa-bench 93b98caf9c72b95766a408a0b04d4c1b95317c39 && \
  download p4l1ly JAltImpact db157709c2c85142b95b95862c8145262c100109 && \
  download p4l1ly symbolicautomata aa0de33a326ee52325499bbfdc11e7ab36970074 && \
  download zimmski aiger ba826db1798022fdabe2de71ea173bd2b6dcac9d && \
  download berkeley-abc abc e463930709e964aede28851114edb77b10d95501 && \
  rm /tmp/download.zip

# TODO one big cabal project instead of local repository

RUN \
  mkdir cabal-repo && \
  cd lens-recursion-schemes && cabal install --lib && cp dist-newstyle/sdist/* ../cabal-repo

RUN \
  cd automata-safa-capnp && /usr/bin/echo -e 'repository local\n  url: file+noindex:///app/cabal-repo\n\npackages: .' > cabal.project && cat cabal.project && cabal update local && cabal install --lib && cp dist-newstyle/sdist/* ../cabal-repo && cd - && \
  :

RUN \
  apt-get install -y cargo && \
  :

RUN \
  cd automata-safa && cargo build --release && cp target/release/libautomata_safa.so /usr/lib && \
  /usr/bin/echo -e 'repository local\n  url: file+noindex:///app/cabal-repo\n\npackages: .' > cabal.project && cat cabal.project && cabal update local && cabal install ltle-to-afa && \
  :

RUN \
  cd ltl-translators && cabal install ltl-generator-exe && cabal install ltl-randgen-exe \
  :
