# # Base image for emacs
FROM jare/emacs as builder
USER root

RUN mkdir -p /opt/build/bin
ENV PATH=${PATH}:/opt/build/bin
WORKDIR /opt/build
ENV SQUIRREL_URL="https://github.com/squirrel-prover/squirrel-prover"
ENV SQUIRREL_DIR_NAME="squirrel-prover"
# Install Squirrel from the main stream repo

RUN apt-get update && apt-get install -y --no-install-recommends pkg-config \
 libpcre3-dev \
 curl 
RUN curl -o opam -fsSL https://github.com/ocaml/opam/releases/download/2.1.2/opam-2.1.2-x86_64-linux
RUN chmod u+x opam && mv opam bin
RUN apt-get install rsync gcc
RUN opam init --disable-sandboxing -a -y --comp 4.12.0


RUN git clone --depth 1 ${SQUIRREL_URL} ${SQUIRREL_DIR_NAME}
WORKDIR ${SQUIRREL_DIR_NAME}
RUN eval `opam config env` && opam install . -y --deps-only
RUN  apt-get install -y --no-install-recommends autoconf libgmp-dev zlib1g-dev

RUN opam install -y alt-ergo
RUN opam install -y why3
RUN  eval `opam config env` && why3 config detect
RUN  eval `opam config env` && make


# We restart from the jare/emacs to reduce the size
FROM jare/emacs
USER root

RUN mkdir -p /opt/build/bin
ENV PATH=${PATH}:/opt/build/bin
RUN mkdir -p /opt/squirrel-prover
RUN mkdir -p /opt/squirrel-prover/examples
RUN mkdir -p /opt/build/bin/theories

# Copy from previous build
COPY --from=builder  /opt/build/squirrel-prover/squirrel /opt/build/bin/
COPY --from=builder /opt/build/squirrel-prover/theories/ /opt/build/bin/theories/
COPY --from=builder /opt/build/squirrel-prover/examples/ /opt/squirrel-prover/examples/

# Proof General
RUN mkdir -p  /root/.emacs.d/lisp
WORKDIR  /root/.emacs.d/lisp
RUN git clone https://github.com/ProofGeneral/PG; cd PG; git checkout ec4f9bad18f6c8336e53910d3ea941d5ceb52f52
RUN mkdir -p /root/.emacs.d/lisp/PG/squirrel
COPY utils/squirrel.el /root/.emacs.d/lisp/PG/squirrel/squirrel.el
COPY utils/squirrel-syntax.el /root/.emacs.d/lisp/PG/squirrel/squirrel-syntax.el
COPY docker/res/proof-site.el /root/.emacs.d/lisp/PG/generic/proof-site.el
COPY docker/res/.emacs /root/.emacs

WORKDIR /opt/squirrel-prover

COPY docker/README.md /opt
# EXPOSE 3001
ENTRYPOINT [] # remove entrypoint from parent image 
CMD ["cat", "/opt/README.md"]
