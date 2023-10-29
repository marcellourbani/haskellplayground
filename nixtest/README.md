# WIP: todo-app

> This folder comes from <https://github.com/juspay/todo-app.git>, to follow <https://zero-to-flakes.com/blog/nixify-haskell-project-intro>

A simple TODO app in Haskell that provides a persistent way to manage the TODO list, by making HTTP requests to Postgrest (postgrest is a web server that converts your PostgreSQL database into a RESTful API).\
\
**This app serves as a hello-world to ultimately demonstrate how a Haskell project can benefit from the use of Nix (to be precise, [haskell-flake](https://haskell.flake.page) and [flake-parts](https://flake.parts)).**

## Prerequisite

- Postgres server
- Postgrest (<https://postgrest.org/en/stable/install.html>)
- Run `./db.sh` to create `data/db.conf` and load the db dump from `db.sql`.
- Run `postgrest data/db.conf` to start the web server.
- `cabal-install` to build the project.

## Getting Started

- Run `cabal install --overwrite-policy="always"` that symlinks `todo-app` executable to your `$HOME/.cabal/bin`
- Run `todo-app view` to see the current list of pending tasks.
- Run `todo-app viewAll` to see the list of completed and pending tasks.
- Run `todo-app add "do something"` to add an item to your list.
- Run `todo-app done 1` to mark the first item as completed.
- Run `todo-app delete 1` to delete the first item from the list.
- Run `todo-app reset` to remove all the items from the list.