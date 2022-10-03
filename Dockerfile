FROM ubuntu:focal-20210921

RUN \
  apt-get update && \
  DEBIAN_FRONTEND=noninteractive apt-get install -y unzip wget software-properties-common cargo build-essential cmake libreadline-dev ant ivy default-jdk maven subversion libboost-dev zsh

RUN \
  ln -s -T /usr/share/java/ivy.jar /usr/share/ant/lib/ivy.jar

RUN \
  add-apt-repository -y ppa:hvr/ghc && \
  apt install -y ghc-8.10.3 cabal-install-3.4 && \
  ln -s /opt/ghc/bin/ghc /usr/local/bin/ghc && \
  ln -s /opt/ghc/bin/cabal /usr/local/bin/cabal && \
  cabal update

WORKDIR /root

# The following chaos is necessary only if you want to use the bisimulation
# model checker or regexlib email benchmarks (it could be simplified a bit if
# only the latter is needed, without the ugly hack of capnproto). Otherwise,
# just do: apt-get install -y capnproto libcapnp-dev
# The JAVA and Cap'n'Proto do not play well (RPC is not supported), so the
# following hacks must be done. Anyway, I'm not a Java expert and all its
# ecosystem seems too complicated for me, so I just make stuff work. All this
# could be maybe done prettier. To sum up: first, a hacked version of capnproto
# is used because I did not have time to continue working on this issue:
# https://github.com/capnproto/capnproto/issues/1070
# Then, all the Capnp-related Java packages are modified to use the hacked
# capnproto.
RUN \
  download() { \
    { \
      wget https://github.com/$1/$2/archive/$3.zip -O /tmp/download.zip && \
      unzip /tmp/download.zip && \
      mv $2-$3 $2 && \
      return 0; \
    } || return 1; \
  }; \
  download p4l1ly capnproto f975947c5e4fa2bfaf5f812411185f20a4d4737d && \
  cd capnproto/c++ && \
  cmake -DCMAKE_POSITION_INDEPENDENT_CODE=ON -S . -B build && \
  cmake --build build && \
  cmake --install build

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
  download p4l1ly lens-recursion-schemes 2dfdf5ec637f8139e3d4cd4b1f0c9803e0477543 && \
  download p4l1ly automata-safa-capnp 38437d30a98ab5b77d0122cc2c82da5cac7cfc07 && \
  download p4l1ly ltl-translators 790508599c04df55a2b862eb13611ef9d9d5fd41 && \
  download p4l1ly JAltImpact db157709c2c85142b95b95862c8145262c100109 && \
  download p4l1ly symbolicautomata 5e27d27059454b607624f8982f97b1aab5f45b5f && \
  download p4l1ly afaminisat 378c06cc720c06cda7e6d48e1685f24fd1c03f78 && \
  rm /tmp/download.zip && \
  mkdir automata-safa
ADD automata-safa.cabal Cargo.lock Cargo.toml CHANGELOG.md LICENSE Setup.hs automata-safa/
ADD app/ automata-safa/app/
ADD src/ automata-safa/src/
ADD test/ automata-safa/test/

RUN \
  cd automata-safa-capnp && \
  cmake -S . -B build && \
  cmake --build build && \
  cmake --install build

RUN \
  cd afaminisat && \
  cmake -S . -B build && \
  cmake --build build

RUN cd JAltImpact && ant resolve && ant build && cp lib/libmathsat5j-5.6.3-sosy0.so /usr/lib/libmathsat5j.so

RUN \
  cd symbolicautomata/automatark && \
  svn export -r95 https://github.com/lorisdanto/automatark/trunk/Parsers && \
  svn export -r95 https://github.com/lorisdanto/automatark/trunk/pom.xml && \
  mvn install && \
  cd ../models && mvn install

# The following chaos is necessary only if you want to use the bisimulation
# model checker or regexlib email benchmarks (it could be simplified a bit if
# only the latter is needed, without the ugly hack of capnproto). Otherwise,
# just do: apt-get install -y capnproto libcapnp-dev
# The JAVA and Cap'n'Proto do not play well (RPC is not supported), so the
# following hacks must be done. Anyway, I'm not a Java expert and all its
# ecosystem seems too complicated for me, so I just make stuff work. All this
# could be maybe done prettier. To sum up: first, a hacked version of capnproto
# is used because I did not have time to continue working on this issue:
# https://github.com/capnproto/capnproto/issues/1070
# Then, all the Capnp-related Java packages are modified to use the hacked
# capnproto.
RUN \
  download() { \
    { \
      wget https://github.com/$1/$2/archive/$3.zip -O /tmp/download.zip && \
      unzip /tmp/download.zip && \
      mv $2-$3 $2 && \
      return 0; \
    } || return 1; \
  }; \
  download capnproto capnproto-java c1cb55e277c94385f9468d0ab50cab7f8f57623b && \
  cd capnproto-java && \
  cmake -S cmake -B build && \
  cmake --build build && \
  cp build/capnpc-java /usr/local/bin && \
  mvn install && \
  \
  cd && \
  download expretio capnp-natives f1732c50f515ad0bab1275bcb522cfdcf2825b0a && \
  cd capnp-natives && \
  cp /usr/local/bin/capnp ../capnproto-java/build/capnpc-java src/main/resources/org/expretio/capnp/natives/linux/x86-64/ && \
  mvn install && \
  \
  cd && \
  download expretio capnp-maven-plugin 28aeb35f47345d34008d699109ae311b0ce9653f && \
  cd capnp-maven-plugin && \
  mvn install && \
  \
  cd ~/automata-safa-capnp && \
  mvn install && \
  \
  cd ~/symbolicautomata/benchmarks && \
  apt-get install -y default-jdk && \
  cmake -S . -B build && \
  cmake --build build && \
  mvn package

RUN echo 'packages: lens-recursion-schemes automata-safa-capnp automata-safa ltl-translators' > cabal.project
RUN cd automata-safa && cargo build --release && cp target/release/libautomata_safa.so /usr/lib
RUN cabal install ltle-to-afa ltl-generator-exe ltl-randgen-exe
RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.bashrc
RUN echo 'export PATH=$PATH:/root/.cabal/bin' >> /root/.zshrc
