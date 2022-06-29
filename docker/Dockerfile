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

# ENV PATH=${PATH}:/opt/build/bin
# RUN apt-get update
# RUN apt-get install -y --no-install-recommends \
#     libc
#     #general stuff
#     libncurses5 \
#     bc \
#     locales \
#     python3 \
#     && rm -rf /var/lib/apt/lists/*

# # set locales so haskell can do its thing
# # https://stackoverflow.com/questions/28405902/how-to-set-the-locale-inside-a-debian-ubuntu-docker-container
# # The following does NOT work -> locale-gen --no-purge en_US.UTF-8
# RUN sed -i '/en_US.UTF-8/s/^# //g' /etc/locale.gen && locale-gen
# ENV LANG en_US.UTF-8
# ENV LANGUAGE en_US:en
# ENV LC_ALL en_US.UTF-8

# # TODO turn variables above into ARGS ..
# # https://stackoverflow.com/questions/52904847/how-do-i-copy-variables-between-stages-of-multi-stage-docker-build
# ENV PROVERIF_DIR_NAME="proverif2.04"
# ENV GSVERIF_DIR_NAME="gsverif"
# ENV DEEPSEC_DIR_NAME="deepsec"
# ENV RES="etc/docker/res"
# ENV CONFIG="etc/docker/config"




# # # Install new maude maude version (not necessary, part of tamarin docker)
# # ENV PRELUDE_MAUDE="${RES}/prelude.maude"
# # ENV MAUDE="${RES}/maude"
# # COPY ${MAUDE} /opt/build/bin/
# # COPY ${PRELUDE_MAUDE} /opt/build/bin/

# COPY ${RES}/proverif-tamarin .
# COPY ${RES}/progsverif-tamarin .
# COPY ${RES}/deepsec-tamarin .
# COPY ${RES}/proverif-tamarin-diff .
# COPY examples/sapic/export examples
# # ENV EXPORT=examples/sapic/export/ExistingSapicModels
# # COPY ${EXPORT}/AC.spthy ${EXPORT}/AC_counter_with_attack.spthy ${EXPORT}/AC_sid_with_attack.spthy ${EXPORT}/AKE.spthy ${EXPORT}/OTP.spthy ${EXPORT}/nsl-no_as-untagged.spthy examples/ExistingSapicModels/
# # COPY examples/sapic/fast examples/fast
# # COPY examples/sapic/slow examples/slow
# # COPY ${RES}/README ${RES}/README-long ${RES}/.bashrc ./
# COPY ${RES}/README-platform ${RES}/.bashrc ./

# ENV PATH=${PATH}:/opt/build/bin:/opt/protocolplatform
# # TODO Do we need this???
# # ENV DEEPSEC_DIR=$DEEPSEC_DIR_IMAGE/deepsec

# EXPOSE 3001
ENTRYPOINT [] # remove entrypoint from parent image 
CMD ["cat", "/opt/protocolplatform/README-platform"]
