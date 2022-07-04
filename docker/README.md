# Running docker

After installing Docker (https://docs.docker.com/engine/install/), the
docker image with Squirrel pre-installed can be obtained with

```
docker pull cjacomme/squirrel-prover:latest
```

The docker image can then be run with

```
docker run -it cjacomme/squirrel-prover:latest bash
```

This should open a bash *inside* the docker, which means that you are
inside a virtual linux machine separated from your computer. You should
land inside a folder with access to the `examples` folder of the
Squirrel prover repository. You can then move inside this folder (`cd
examples`) and run one of the examples, e.g. with `emacs
basic-hash.sp`. 

Note that this gives you a basic access to Emacs using the
command-line interface of the terminal (no mouse support). Also, this
is a sandbox: the other files on your computer are not accessible.

## Accessing files from outside the docker

To access files from a folder on your computer at
`<path_to_your_workspace>`, run 
```
docker run -it -v \
 <path_to_your_workspace>:/opt/squirrel-prover/MyComputer \
 cjacomme/squirrel-prover:latest bash
```

This populates the `MyComputer` folder, next to the `examples` one,
with the given path.


## Runing Emacs in GUI mode in the browser

The simplest way to display a gui Emacs is by using a webserver, using
a second docker image. Obtain it with:
```
docker pull jare/x11-bridge:latest
```

Then, run the two following commands inside a terminal (if you are on
MAC OS, you need to have `docker-desktop` running in the
background, see https://docs.docker.com/desktop/mac/install/):
```
docker run -d \
 --name x11-bridge \
 -e MODE="tcp" \
 -e XPRA_HTML="yes" \
 -e DISPLAY=:14 \
 -e XPRA_PASSWORD=111 \
 -p 10000:10000 \
 jare/x11-bridge

docker run -d \
 --name emacs-sp \
 --volumes-from x11-bridge \
 -e DISPLAY=:14 \
 cjacomme/squirrel-prover emacs
 ```

Then, visit
`http://localhost:10000/index.html?encoding=rgb32&password=111` to
obtain a display of a GUI Emacs, in which you can open files inside
the docker. Before opening a file, we recomend that you resize the
Emacs window to be larger by a drag and drop on the top left corner of
the Emacs window (inside the browser). Making the window full screen
may lead to low resolution and lags.

To kill the dockers, simply run `docker rm -f x11-bridge emacs-sp`
(this kills both dockers). You can add your own folder as before, 
by replacing the commands above with
```
docker run -d \
 --name x11-bridge \
 -e MODE="tcp" \
 -e XPRA_HTML="yes" \
 -e DISPLAY=:14 \
 -e XPRA_PASSWORD=111 \
 -v <path_to_your_workspace>:/opt/squirrel-prover/MyComputer \
 -p 10000:10000 \
 jare/x11-bridge
 
docker run -d \
 --name emacs-sp \
 --volumes-from x11-bridge \
 -e DISPLAY=:14 \
 cjacomme/squirrel-prover emacs
 ```

# Compiling and pushing the docker

Run `./docker/build.sh` to build from scratch the image. `docker/res`
contains the `.emacs` used by the docker, as well as the updated
`proof-site.el` file from a fixed commit of PG.

To publish the image, see @Charlie JACOMME (Dockerhub does not support
free organizations...), which is then done by running:
```
docker tag sp/squirrel-prover \
 cjacomme/squirrel-prover:latest; \
 docker push cjacomme/squirrel-prover:latest
```

