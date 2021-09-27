import os


class ssh_session:
    def __init__(self, user, host, port=22, avoidTimeout=False):
        print('\nOpen tunnel connection to server.')
        self.user_host = '{}@{}'.format(user, host)
        self.port = port
        self.socket = '~/.ssh/{}'.format(self.user_host)
        if avoidTimeout:
            option = '-o serverAliveInterval=120'
        else:
            option = ''
        os.system('ssh -M -f -N -o ControlPath={} {} -p {} {}'.format(self.socket, option, self.port, self.user_host))

    def __del__(self):
        print('\nClose connection.')
        os.system('ssh -S {} -O exit {}'.format(self.socket, self.user_host))

    def get_param(self):
        return 'ssh -S {} -p {} {}'.format(self.socket, self.port, self.user_host)

    def run_commands(self, cmd):
        with open('ssh_commands.sh', 'w') as cmd_file:
            cmd_file.write(cmd)
        os.system(
            'cat ssh_commands.sh | ssh -T -S {} -p {} {}'.format(self.socket, self.port, self.user_host))
        os.remove('ssh_commands.sh')

    def copy_to(self, source, destination):
        os.system('rsync -avz -e "ssh -o ControlPath={socket} -p {port}" {source} {server}:{dest}'.format(
            socket=self.socket,
            port=self.port,
            source=source,
            server=self.user_host,
            dest=destination
        ))

    def copy_from(self, source, destination):
        os.system('rsync -avz -e "ssh -o ControlPath={socket} -p {port}" {server}:{source} {dest}'.format(
            socket=self.socket,
            port=self.port,
            source=source,
            server=self.user_host,
            dest=destination
        ))

    def clean(self, folderPath):
        rmCmd = 'rm -r {folderPath}'.format(folderPath=folderPath)
        mkdirCmd = 'mkdir {folderPath}'.format(folderPath=folderPath)
        self.run_commands(rmCmd)
        self.run_commands(mkdirCmd)