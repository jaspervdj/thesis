#!/usr/bin/env ruby

require 'fileutils'
require 'open3'
require 'tempfile'

TMP = 'tmp'
ROOT = FileUtils.pwd

def valid_name(name)
  !name.include?('$')
end

def compile(command, name)
  print "Compiling #{name}: "

  start = Time.now
  output = `#{command}`
  status = $?

  elapsed = (Time.now - start).floor
  if status.success? then
    print "success (#{elapsed}s)\n"
  else
    print "exit code #{status.exitstatus} (#{elapsed}s)\n"
  end

  return output
end

def compile_cabal(name)
  package = name.chomp('.tar.gz')
  `tar -xzf #{name}`

  FileUtils.cd package
  cabal_file = Dir.glob('*.cabal').first

  patched = File.read(cabal_file).gsub(/^(library)(\s+)/i) do
    "#{$1}#{$2}" +
      "build-depends: what-morphism#{$2}" +
      "ghc-options: -fplugin=WhatMorphism#{$2}"
  end

  File.open(cabal_file, 'w') { |f| f.write(patched) }

  command = 'cabal configure && cabal build 2>&1'
  output = compile(command, package)

  FileUtils.cd ROOT
  FileUtils.rm_r package

  # Write log
  log = "#{package}.log"
  File.open(log, 'w') { |f| f.write(output) }
  puts "Log written to #{log}"
end

file = ARGV[0]

if file.end_with? '.zip'
  compile_zip(file)
elsif file.end_with? '.tar.gz'
  compile_cabal(file)
end
